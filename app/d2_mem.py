"""Read-only access to Minecraft Dungeons II's memory (like a performance monitor would).

Nothing is ever written to the game and no code is injected - the game's code protection is
untouched. Used to read exact buff timers straight from the game's data.
"""
import ctypes
import ctypes.wintypes as wt
import struct
import subprocess
import time

GAME_EXE = "Dungeons-Win64-Shipping.exe"
k32 = ctypes.windll.kernel32
k32.OpenProcess.restype = wt.HANDLE
k32.ReadProcessMemory.argtypes = [wt.HANDLE, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t,
                                  ctypes.POINTER(ctypes.c_size_t)]
k32.CreateToolhelp32Snapshot.restype = wt.HANDLE
k32.CloseHandle.argtypes = [wt.HANDLE]
k32.GetExitCodeProcess.argtypes = [wt.HANDLE, ctypes.POINTER(ctypes.c_ulong)]
PROCESS_VM_READ, PROCESS_QUERY_LIMITED = 0x10, 0x1000


class MODULEENTRY32W(ctypes.Structure):
    _fields_ = [("dwSize", wt.DWORD), ("th32ModuleID", wt.DWORD), ("th32ProcessID", wt.DWORD),
                ("GlblcntUsage", wt.DWORD), ("ProccntUsage", wt.DWORD), ("modBaseAddr", ctypes.c_void_p),
                ("modBaseSize", wt.DWORD), ("hModule", wt.HMODULE), ("szModule", ctypes.c_wchar * 256),
                ("szExePath", ctypes.c_wchar * 260)]


k32.Module32FirstW.argtypes = [wt.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
k32.Module32NextW.argtypes = [wt.HANDLE, ctypes.POINTER(MODULEENTRY32W)]


class PROCESSENTRY32W(ctypes.Structure):
    _fields_ = [("dwSize", wt.DWORD), ("cntUsage", wt.DWORD), ("th32ProcessID", wt.DWORD),
                ("th32DefaultHeapID", ctypes.c_void_p), ("th32ModuleID", wt.DWORD), ("cntThreads", wt.DWORD),
                ("th32ParentProcessID", wt.DWORD), ("pcPriClassBase", ctypes.c_long), ("dwFlags", wt.DWORD),
                ("szExeFile", ctypes.c_wchar * 260)]


k32.Process32FirstW.argtypes = [wt.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
k32.Process32NextW.argtypes = [wt.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]


def find_pid(name=GAME_EXE):
    """Process list straight from Windows (no tasklist process every few seconds while idle)."""
    snap = k32.CreateToolhelp32Snapshot(0x2, 0)  # TH32CS_SNAPPROCESS
    if not snap or snap == wt.HANDLE(-1).value:
        return None
    pe = PROCESSENTRY32W()
    pe.dwSize = ctypes.sizeof(pe)
    try:
        ok = k32.Process32FirstW(snap, ctypes.byref(pe))
        while ok:
            if pe.szExeFile.lower() == name.lower():
                return pe.th32ProcessID
            ok = k32.Process32NextW(snap, ctypes.byref(pe))
    finally:
        k32.CloseHandle(snap)
    return None


def module(pid, name=GAME_EXE):
    snap = k32.CreateToolhelp32Snapshot(0x18, pid)
    me = MODULEENTRY32W()
    me.dwSize = ctypes.sizeof(me)
    ok = k32.Module32FirstW(snap, ctypes.byref(me))
    try:
        while ok:
            if me.szModule.lower() == name.lower():
                return me.modBaseAddr, me.modBaseSize
            ok = k32.Module32NextW(snap, ctypes.byref(me))
    finally:
        k32.CloseHandle(snap)
    return None, None


class Game:
    def __init__(self):
        self.pid = find_pid()
        if not self.pid:
            raise RuntimeError("game not running")
        self.h = k32.OpenProcess(PROCESS_VM_READ | PROCESS_QUERY_LIMITED, False, self.pid)
        if not self.h:
            raise RuntimeError("cannot open game process")
        try:
            self.base, self.size = module(self.pid)
            if not self.base:
                raise RuntimeError("game module not found yet")
            self.sections = self._sections()
        except Exception:
            self.close()
            raise

    def close(self):
        if self.h:
            k32.CloseHandle(self.h)
            self.h = None

    # ---- raw reads
    def read(self, addr, n):
        if not addr or n <= 0:
            return None
        buf = ctypes.create_string_buffer(n)
        got = ctypes.c_size_t()
        if not k32.ReadProcessMemory(self.h, ctypes.c_void_p(addr), buf, n, ctypes.byref(got)) or got.value != n:
            return None
        return buf.raw

    def u64(self, a):
        b = self.read(a, 8)
        return struct.unpack("<Q", b)[0] if b else None

    def i32(self, a):
        b = self.read(a, 4)
        return struct.unpack("<i", b)[0] if b else None

    def f32(self, a):
        b = self.read(a, 4)
        return struct.unpack("<f", b)[0] if b else None

    def f64(self, a):
        b = self.read(a, 8)
        return struct.unpack("<d", b)[0] if b else None

    def _sections(self):
        hdr = self.read(self.base, 0x1000)
        pe = struct.unpack_from("<I", hdr, 0x3C)[0]
        n = struct.unpack_from("<H", hdr, pe + 6)[0]
        opt = struct.unpack_from("<H", hdr, pe + 20)[0]
        out = {}
        o = pe + 24 + opt
        for _ in range(n):
            name = hdr[o:o + 8].rstrip(b"\0").decode(errors="replace")
            vsize, vaddr = struct.unpack_from("<II", hdr, o + 8)
            out[name] = (self.base + vaddr, vsize)
            o += 40
        return out


# --------------------------------------------------------------------------
# Unreal reflection (layouts measured for this game's UE 5.6 build)
# --------------------------------------------------------------------------
FNAMEPOOL_RVA = 0xBE71F40     # FNameEntryAllocator: lock, CurrentBlock, CurrentByteCursor, Blocks[]
GUOBJECTARRAY_RVA = 0xBF55AF0
OBJ_CLASS, OBJ_NAME, OBJ_OUTER = 0x10, 0x18, 0x20
STRUCT_SUPER, STRUCT_CHILDPROPS = 0x40, 0x50
FFIELD_CLASS, FFIELD_NEXT, FFIELD_NAME = 0x08, 0x18, 0x20
FPROP_OFFSET = 0x48
PROP_INNER = 0x80             # FArrayProperty::Inner
PROP_STRUCT = 0x78            # FStructProperty::Struct
PROP_CLASS = 0x78             # FObjectPropertyBase::PropertyClass


class Reflection:
    def __init__(self, game):
        self.g = game
        self.pool = game.base + FNAMEPOOL_RVA
        self.names = {}
        self._props = {}
        self.item_size = 0x18
        self._cls_names, self._is_a = {}, {}
        self._refresh_count()

    def _refresh_count(self):
        # the object array keeps growing while the game loads levels: re-read it before each scan
        oa = self.g.base + GUOBJECTARRAY_RVA
        self.objects_ptr = self.g.u64(oa + 0x10) or 0
        self.num = self.g.i32(oa + 0x24) or 0

    def name(self, index):
        if index in self.names:
            return self.names[index]
        block, offset = index >> 16, (index & 0xFFFF) * 2
        bp = self.g.u64(self.pool + 0x10 + block * 8)
        hdr = self.g.read(bp + offset, 2) if bp else None
        if not hdr:
            return None
        h = struct.unpack("<H", hdr)[0]
        wide, ln = h & 1, h >> 6
        raw = self.g.read(bp + offset + 2, ln * (2 if wide else 1))
        s = raw.decode("utf-16-le" if wide else "latin-1", errors="replace") if raw else None
        self.names[index] = s
        return s

    def fname(self, addr):
        b = self.g.read(addr, 8)
        if not b:
            return None
        idx, num = struct.unpack("<II", b)
        n = self.name(idx)
        return n if not num else f"{n}_{num - 1}"

    def obj_name(self, obj):
        return self.fname(obj + OBJ_NAME)

    def class_of(self, obj):
        return self.g.u64(obj + OBJ_CLASS)

    def class_name(self, obj):
        c = self.class_of(obj)
        if not c:
            return None
        if c not in self._cls_names:  # classes live for the whole session: name them once
            self._cls_names[c] = self.obj_name(c)
        return self._cls_names[c]

    def objects(self):
        """Yield every live UObject pointer."""
        chunk_size = 65536
        self._refresh_count()
        nchunks = (self.num + chunk_size - 1) // chunk_size
        for c in range(nchunks):
            cp = self.g.u64(self.objects_ptr + c * 8)
            if not cp:
                continue
            n = min(chunk_size, self.num - c * chunk_size)
            blob = self.g.read(cp, n * self.item_size)
            if not blob:
                continue
            for i in range(n):
                o = struct.unpack_from("<Q", blob, i * self.item_size)[0]
                if o:
                    yield o

    def find_objects(self, class_name):
        out = []
        for o in self.objects():
            if self.class_name(o) == class_name:
                out.append(o)
        return out

    def is_a(self, obj, class_name):
        c0 = self.class_of(obj)
        key = (c0, class_name)
        if key not in self._is_a:
            self._is_a[key] = self._class_is_a(c0, class_name)
        return self._is_a[key]

    def _class_is_a(self, c, class_name):
        while c:
            if self.obj_name(c) == class_name:
                return True
            c = self.g.u64(c + STRUCT_SUPER)
        return False

    def properties(self, struct_obj):
        """{name: (offset, property ptr, property class name)} including inherited ones."""
        if struct_obj in self._props:
            return self._props[struct_obj]
        out = {}
        s = struct_obj
        while s:
            p = self.g.u64(s + STRUCT_CHILDPROPS)
            while p:
                pname = self.fname(p + FFIELD_NAME)
                fc = self.g.u64(p + FFIELD_CLASS)
                pclass = self.name(self.g.i32(fc)) if fc else None
                if pname and pname not in out:
                    out[pname] = (self.g.i32(p + FPROP_OFFSET), p, pclass)
                p = self.g.u64(p + FFIELD_NEXT)
            s = self.g.u64(s + STRUCT_SUPER)
        self._props[struct_obj] = out
        return out


# --------------------------------------------------------------------------
# Exact buffs: the local player's Gameplay Ability System active effects
# --------------------------------------------------------------------------
WORLD_TIME_SECONDS = 0x798    # UWorld::TimeSeconds (double), found by watching it tick 1.0/s
GE_ELEMENT_SIZE = 864         # sizeof(FActiveGameplayEffect)
GE_SPEC = 0x18
GE_SPEC_DEF, GE_SPEC_DURATION, GE_SPEC_STACKS = 0x0, 0x50, 0x1C0
GE_START_WORLD_TIME = 0x2D8
GE_SPEC_DYN_TAGS = 0x170        # FGameplayEffectSpec::DynamicGrantedTags (TArray<FName-sized tags>)


class BuffReader:
    """Polls the local player's active gameplay effects. Read-only."""

    def __init__(self):
        self.g = Game()
        self.r = Reflection(self.g)
        self.pc = self.pawn = self.asc = self.world = None
        self._asc_props = None
        self._def_names = {}
        self.last_find = 0.0
        self._attrs = None    # [(key, address of FGameplayAttributeData)]
        self.imc = None       # InventoryManagerComponent (equipped items)

    def _find_player(self):
        r, g = self.r, self.g
        self.pc = self.pawn = self.asc = self.world = self.imc = None
        self._attrs = None
        objs = list(r.objects())
        for o in objs:
            if not r.is_a(o, "PlayerController") or (r.obj_name(o) or "").startswith("Default__"):
                continue
            cp = r.properties(r.class_of(o))
            if not g.u64(o + cp["Player"][0]):
                continue  # not the local player's controller
            self.pc = o
            self.pawn = g.u64(o + cp["Pawn"][0])
            level = g.u64(o + OBJ_OUTER)
            self.world = g.u64(level + OBJ_OUTER) if level else None
            break
        if not self.pawn:
            return
        pp = r.properties(r.class_of(self.pawn))
        if "InventoryManagerComponent" in pp:
            self.imc = g.u64(self.pawn + pp["InventoryManagerComponent"][0])
            ip = r.properties(r.class_of(self.imc)) if self.imc else {}
            if "ReplicatedItems" in ip:
                self._items_off = ip["ReplicatedItems"][0] + 0x108  # SlotEntryContainerReplicated::Items
            else:
                self.imc = None  # inventory not spawned yet: found again on the next check
        for o in objs:
            if r.class_name(o) != "SWAbilitySystemComponent":
                continue
            if self._asc_props is None:
                self._asc_props = r.properties(r.class_of(o))
            if g.u64(o + self._asc_props["AvatarActor"][0]) == self.pawn:
                self.asc = o
                break

    def alive(self):
        """False once the game process has exited (or been relaunched)."""
        code = ctypes.c_ulong()
        if not k32.GetExitCodeProcess(self.g.h, ctypes.byref(code)) or code.value != 259:  # STILL_ACTIVE
            return False
        return True

    def _still_valid(self):
        """The cached player chain still points at the live local player (level loads and
        respawns replace the pawn/ASC; freed memory can still read as something)."""
        g, r = self.g, self.r
        if g.u64(self.asc + OBJ_CLASS) is None or not self.pc:
            return False
        cp = r.properties(r.class_of(self.pc)) if r.class_of(self.pc) else None
        if not cp or "Pawn" not in cp or g.u64(self.pc + cp["Pawn"][0]) != self.pawn:
            return False
        if g.u64(self.asc + self._asc_props["AvatarActor"][0]) != self.pawn:
            return False
        if self.pawn and "InventoryManagerComponent" in (pp := r.properties(r.class_of(self.pawn)) or {}):
            if g.u64(self.pawn + pp["InventoryManagerComponent"][0]) != self.imc:
                return False
        level = g.u64(self.pc + OBJ_OUTER)
        return (g.u64(level + OBJ_OUTER) if level else None) == self.world

    ATTRS = {"ATR_Health": ("Health", "HealthMax", "HealthPotionCharges", "HealthPotionChargesMax",
                            "HealthPotionBaseCooldown", "HealthPotionCooldownMultiplier"),
             "ATR_Soul": ("Souls", "SoulsMax")}

    def _find_attrs(self):
        g, r = self.g, self.r
        off = self._asc_props["SpawnedAttributes"][0]
        data, num = g.u64(self.asc + off), g.i32(self.asc + off + 8)
        out = []
        for i in range(num or 0):
            s = g.u64(data + i * 8)
            cn = r.class_name(s) if s else None
            if cn in self.ATTRS:
                props = r.properties(r.class_of(s))
                for k in self.ATTRS[cn]:
                    if k in props:
                        out.append((k, s + props[k][0] + 12))  # FGameplayAttributeData::CurrentValue
        if {"Health", "Souls"} - {k for k, _ in out}:
            self._attrs = None  # attribute sets not spawned yet: look again shortly
            self._attrs_retry = time.perf_counter() + 1.0
            return out
        self._attrs = out

    def attributes(self):
        if self._attrs is None:
            if time.perf_counter() < getattr(self, "_attrs_retry", 0.0):
                return {}
            found = self._find_attrs()
            if self._attrs is None:
                return {k: self.g.f32(a) for k, a in found}
        return {k: self.g.f32(a) for k, a in self._attrs}

    def equipped(self):
        """{slot tag: item type tag} for equipped items, e.g.
        'SW.ItemSlot.Equipment.Artifact.Slot2': 'SW.Item.Artifact.HasteMushroom'."""
        g, r = self.g, self.r
        if not self.imc:
            return {}
        data, num = g.u64(self.imc + self._items_off), g.i32(self.imc + self._items_off + 8)
        if not data or not num or not 0 < num < 128:
            return {}
        blob = g.read(data, num * 0x50)  # SlotEntry
        if not blob:
            return {}
        out = {}
        for i in range(num):
            slot = r.name(struct.unpack_from("<I", blob, i * 0x50 + 0xC)[0])
            if not slot or ".Equipment." not in slot:
                continue
            ip, inum = struct.unpack_from("<Qi", blob, i * 0x50 + 0x40)  # ItemInventoryEntries
            if ip and inum > 0:
                tag = g.read(ip, 4)  # InventoryEntry.ItemData.TypeTag (FName index)
                out[slot] = r.name(struct.unpack("<I", tag)[0]) if tag else None
        return out

    def def_name(self, d):
        """Effect definition name: the asset name for data-driven SWGameplayEffect instances
        (e.g. SW_Status_Strength_GE), otherwise the effect's class name."""
        if d not in self._def_names:
            c = self.r.class_of(d)
            cn = self.r.obj_name(c) if c else None
            self._def_names[d] = self.r.obj_name(d) if cn == "SWGameplayEffect" else cn
        return self._def_names[d]

    def tags(self, elem_blob, e, off):
        tp, tn = struct.unpack_from("<Qi", elem_blob, e + off)
        if not tp or not 0 < tn < 32:
            return []
        raw = self.g.read(tp, tn * 8)
        return [self.r.name(struct.unpack_from("<I", raw, k * 8)[0]) for k in range(tn)] if raw else []

    def poll(self, now):
        """(buffs, cooldowns) or None if the game/player isn't available.
        buffs: [(effect name, remaining s or -1 if infinite, duration, stacks)]
        cooldowns: {"Artifact1".."Artifact3"/...: (remaining, duration)}"""
        g = self.g
        if now - self.last_find > 2.0:
            # a full object scan is slow: at most every 2 s, even while no player exists (menus)
            self.last_find = now
            if self.asc is None or not self._still_valid():
                self._def_names.clear()
                self._find_player()
        if self.asc is None or self.world is None:
            return None
        wt = g.f64(self.world + WORLD_TIME_SECONDS)
        arr = self.asc + self._asc_props["ActiveGameplayEffects"][0] + 0x130
        data, num = g.u64(arr), g.i32(arr + 8)
        if wt is None or data is None or num is None or not (0 <= num < 512):
            self.asc = None
            return None
        blob = g.read(data, num * GE_ELEMENT_SIZE) if num else b""
        if blob is None:
            self.asc = None
            return None
        buffs, cds = [], {}
        for i in range(num):
            e = i * GE_ELEMENT_SIZE
            d = struct.unpack_from("<Q", blob, e + GE_SPEC + GE_SPEC_DEF)[0]
            dur = struct.unpack_from("<f", blob, e + GE_SPEC + GE_SPEC_DURATION)[0]
            stacks = struct.unpack_from("<i", blob, e + GE_SPEC + GE_SPEC_STACKS)[0]
            start = struct.unpack_from("<f", blob, e + GE_START_WORLD_TIME)[0]
            name = self.def_name(d) if d else None
            rem = -1.0 if dur <= 0 else max(0.0, start + dur - wt)
            if name == "GE_AbilityCooldown":
                for tag in self.tags(blob, e, GE_SPEC + GE_SPEC_DYN_TAGS):
                    if tag and tag.startswith("SW.AbilityCallsign."):
                        key = tag.split(".")[-1]
                        if key not in cds or rem > cds[key][0]:
                            cds[key] = (rem, dur)
            else:
                buffs.append((name, rem, dur, stacks))
        return buffs, cds, self.attributes(), self.equipped()
