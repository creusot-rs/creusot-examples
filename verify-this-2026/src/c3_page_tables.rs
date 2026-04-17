// Challenge 3 of VerifyThis 2026: Multi-level page tables
//
// https://verifythis.github.io/onsite/archive/2026/challenge3.pdf
//
// Completed (Q1 of 5):
// - Machine invariant
// - Safety and correctness of translation (wrt. to a Pearlite implementation)
// - Injectivity of translation

use creusot_std::{logic::FMap, prelude::*};

pub struct Mem([u8; 2usize.pow(32)]);

pub struct Table(Seq<u32>);

impl Table {
    #[logic]
    #[requires(inv(self))]
    #[requires((lo & 0x3FFu32) == 0u32)]
    pub fn encoded_in(self, mem: Mem, lo: u32) -> bool {
        pearlite! {
            forall<i: u32> 0 <= i@ && i@ < 0x100 ==>
                mem.0@[(lo | (i << 2u32))@] == self.0[i@] as u8 &&
                mem.0@[(lo | (i << 2u32) + 1u32)@] == (self.0[i@] >> 8u32) as u8 &&
                mem.0@[(lo | (i << 2u32) + 2u32)@] == (self.0[i@] >> 0x10u32) as u8 &&
                mem.0@[(lo | (i << 2u32) + 3u32)@] == (self.0[i@] >> 0x18u32) as u8
        }
    }

    #[logic]
    #[requires(0u32 <= i && i < 0x100u32)]
    pub fn get(self, i: u32) -> Option<u32> {
        pearlite! {
            if self.0[i@] & 1u32 == 0u32 { None }
            else { Some(self.0[i@] & !1u32) }
        }
    }

    #[logic]
    pub fn disjoint_from(self, other: Table) -> bool {
        pearlite! {
            forall<i1, i2, p1, p2>
                self.get(i1) == Some(p1) ==>
                other.get(i2) == Some(p2) ==>
                p1 != p2
        }
    }
}

impl Invariant for Table {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! {
            self.0.len() == 0x100 &&
            (forall<i, p> self.get(i) == Some(p) ==> p & 0x3FFu32 == 0u32) &&
            (forall<i> self.get(i) == None ==> self.0[i@] == 0u32) &&
            (forall<i1, i2, p1, p2>
                self.get(i1) == Some(p1) ==>
                self.get(i2) == Some(p2) ==>
                p1 == p2 ==>
                i1 == i2)
        }
    }
}

pub struct Machine {
    mem: Mem,
    m_next: u32,
    h_next: u32,

    table_lvl0: Snapshot<Table>,
    #[allow(dead_code)]
    tables_lvl1: Snapshot<FMap<u32, Table>>,
    #[allow(dead_code)]
    tables_lvl2: Snapshot<FMap<u32, Table>>,
}

pub const H_START: u32 = 0x2000000;

impl Invariant for Machine {
    #[logic(inline, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            inv(*self.table_lvl0) &&
            self.table_lvl0.encoded_in(self.mem, 0u32) &&
            (forall<j, p> self.table_lvl0.get(j) == Some(p) ==> self.tables_lvl1.contains(p)) &&

            (forall<i, t>
                self.tables_lvl1.get(i) == Some(t) ==>
                inv(t) &&
                1024u32 <= i && i < self.m_next && (i & 0x3FFu32 == 0u32) &&
                t.encoded_in(self.mem, i) &&
                (forall<j, p> t.get(j) == Some(p) ==> self.tables_lvl2.contains(p)) &&
                t.disjoint_from(*self.table_lvl0) &&
                (forall<j, tt> i != j ==> self.tables_lvl1.get(j) == Some(tt) ==> tt.disjoint_from(t))
            ) &&

            (forall<i, t>
                self.tables_lvl2.get(i) == Some(t) ==>
                inv(t) &&
                1024u32 <= i && i < self.m_next && (i & 0x3FFu32 == 0u32) &&
                t.encoded_in(self.mem, i) &&
                (forall<j, p> t.get(j) == Some(p) ==> p >= H_START)  &&
                t.disjoint_from(*self.table_lvl0) &&
                (forall<j, tt> self.tables_lvl1.get(j) == Some(tt) ==> tt.disjoint_from(t)) &&
                (forall<j, tt> i != j ==> self.tables_lvl2.get(j) == Some(tt) ==> tt.disjoint_from(t)))
        }
    }
}

impl Mem {
    #[ensures(result == self.0@[paddr@])]
    fn read_u8(&self, paddr: u32) -> u8 {
        self.0[paddr as usize]
    }

    #[ensures((^self).0@ == self.0@.set(paddr@, v))]
    fn write_u8(&mut self, paddr: u32, v: u8) {
        self.0[paddr as usize] = v
    }

    #[requires(paddr & 3u32 == 0u32)]
    #[ensures(result
        ==
            (self.0@[paddr@] as u32) |
            ((self.0@[(paddr + 1u32)@] as u32) << 8u32) |
            ((self.0@[(paddr + 2u32)@] as u32) << 16u32) |
            ((self.0@[(paddr + 3u32)@] as u32) << 24u32))]
    #[ensures(
            self.0@[paddr@] == result as u8 &&
            self.0@[(paddr + 1u32)@] == (result >> 8u32) as u8 &&
            self.0@[(paddr + 2u32)@] == (result >> 0x10u32) as u8 &&
            self.0@[(paddr + 3u32)@] == (result >> 0x18u32) as u8)]
    #[bitwise_proof]
    fn read_u32(&self, paddr: u32) -> u32 {
        (self.read_u8(paddr) as u32)
            | ((self.read_u8(paddr + 1) as u32) << 8u32)
            | ((self.read_u8(paddr + 2) as u32) << 16u32)
            | ((self.read_u8(paddr + 3) as u32) << 24u32)
    }

    #[allow(unused)]
    #[requires(paddr & 3u32 == 0u32)]
    #[ensures((^self).0@ == (*self).0@
        .set(paddr@, v as u8)
        .set((paddr + 1u32)@, (v >> 8u32) as u8)
        .set((paddr + 2u32)@, (v >> 16u32) as u8)
        .set((paddr + 3u32)@, (v >> 24u32) as u8))]
    #[bitwise_proof]
    fn write_u32(&mut self, paddr: u32, v: u32) {
        self.write_u8(paddr, v as u8);
        self.write_u8(paddr + 1, (v >> 8u32) as u8);
        self.write_u8(paddr + 2, (v >> 16u32) as u8);
        self.write_u8(paddr + 3, (v >> 24u32) as u8);
    }

    #[allow(unused_variables)]
    #[requires(table.encoded_in(*self, p & !1023u32))]
    #[requires(p & 3u32 == 0u32)]
    #[ensures(result == table.get((p & 1023u32) >> 2u32))]
    #[bitwise_proof]
    fn read_table(&self, p: u32, table: Snapshot<Table>) -> Option<u32> {
        let r = self.read_u32(p);
        if r & 1 == 0 {
            return None;
        } else {
            return Some(r & !1);
        }
    }
}

impl Machine {
    #[logic]
    pub fn translate_log(self, vaddr: u32) -> Option<u32> {
        let k = vaddr >> 26u32;
        let i = (vaddr >> 18u32) & 255u32;
        let j = (vaddr >> 10u32) & 255u32;
        let o = vaddr & 1023u32;

        match self.table_lvl0.get(k) {
            Some(t) => match self.tables_lvl1[t].get(i) {
                Some(m) => match self.tables_lvl2[m].get(j) {
                    Some(p) => Some(p + o),
                    None => None,
                },
                None => None,
            },
            None => None,
        }
    }

    #[logic]
    #[requires(self.translate_log(vaddr1) != None)]
    #[requires(self.translate_log(vaddr2) != None)]
    #[requires(vaddr1 != vaddr2)]
    #[requires(inv(self))]
    #[ensures(self.translate_log(vaddr1) != self.translate_log(vaddr2))]
    #[bitwise_proof]
    pub fn translate_log_inj(self, vaddr1: u32, vaddr2: u32) {
        pearlite! {
            let k1 = vaddr1 >> 26u32;
            let i1 = (vaddr1 >> 18u32) & 255u32;
            let j1 = (vaddr1 >> 10u32) & 255u32;
            let o1 = vaddr1 & 1023u32;


            let k2 = vaddr2 >> 26u32;
            let i2 = (vaddr2 >> 18u32) & 255u32;
            let j2 = (vaddr2 >> 10u32) & 255u32;
            let o2 = vaddr2 & 1023u32;


            match self.table_lvl0.get(k1) {
                Some(t1) => match self.tables_lvl1.get(t1) {
                    Some(st1) => match st1.get(i1) {
                        Some(m1) => match self.tables_lvl2.get(m1) {
                            Some(sm1) => match sm1.get(j1) {
                                Some(p1) => {
                                    proof_assert!(self.translate_log(vaddr1) == Some(p1 + o1));
                                    proof_assert!(inv(sm1));
                                    proof_assert!(p1 & 1023u32 == 0u32);
                                    match self.table_lvl0.get(k2) {
                                        Some(t2) => match self.tables_lvl1.get(t2) {
                                            Some(st2) => match st2.get(i2) {
                                                Some(m2) => match self.tables_lvl2.get(m2) {
                                                    Some(sm2) => match sm2.get(j2) {
                                                        Some(p2) => {
                                                            proof_assert!(self.translate_log(vaddr2) == Some(p2 + o2));
                                                            proof_assert!(inv(sm2));
                                                            proof_assert!(p2 & 1023u32 == 0u32);
                                                            if k1 != k2 {
                                                                proof_assert!(t1 != t2);
                                                                proof_assert!(st1.disjoint_from(st2));
                                                                proof_assert!(m1 != m2);
                                                                proof_assert!(sm1.disjoint_from(sm2));
                                                                proof_assert!(p1 != p2);
                                                            } else if i1 != i2 {
                                                                proof_assert!(t1 == t2);
                                                                proof_assert!(m1 != m2);
                                                                proof_assert!(sm1.disjoint_from(sm2));
                                                                proof_assert!(p1 != p2);
                                                            } else if j1 != j2 {
                                                                proof_assert!(t1 == t2);
                                                                proof_assert!(st1 == st2);
                                                                proof_assert!(m1 == m2);
                                                                proof_assert!(sm1 == sm2);
                                                                proof_assert!(p1 != p2);
                                                            }
                                                        },
                                                        None => ()
                                                    }
                                                    None => ()
                                                }
                                                None => ()
                                            }
                                            None => ()
                                        }
                                        None => ()
                                    }
                                }
                                None => ()
                            }
                            None => ()
                        }
                        None => ()
                    }
                    None => ()
                }
                None => (),
            }
        }
    }

    #[ensures(result == self.translate_log(vaddr))]
    #[bitwise_proof]
    pub fn translate(&self, vaddr: u32) -> Option<u32> {
        let k = vaddr >> 26;
        proof_assert!(k == vaddr >> 26u32);
        let i = (vaddr >> 18) & 255;
        proof_assert!(i == (vaddr >> 18u32) & 255u32);
        let j = (vaddr >> 10) & 255;
        proof_assert!(j == (vaddr >> 10u32) & 255u32);
        let o = vaddr & 1023;
        proof_assert!(o == vaddr & 1023u32);

        let t = self.mem.read_table(k << 2, self.table_lvl0)?;
        proof_assert!(self.table_lvl0.get(k) == Some(t));

        proof_assert!(self.tables_lvl1[t].encoded_in(self.mem, t));
        let m = self
            .mem
            .read_table(t | (i << 2), snapshot!(self.tables_lvl1[t]))?;
        proof_assert!(self.tables_lvl1[t].get(i) == Some(m));

        proof_assert!(self.tables_lvl2[m].encoded_in(self.mem, m));
        let p = self
            .mem
            .read_table(m | (j << 2), snapshot!(self.tables_lvl2[m]))?;
        proof_assert!(self.tables_lvl2[m].get(j) == Some(p));

        Some(p + o)
    }

    // Nothing proved beyond this point

    #[allow(unused)]
    #[trusted]
    fn zero_page_out(&mut self, paddr: u32) {
        assert!(paddr & 1023 == 0, "Physical address must be page-aligned");
        for i in 0..0x100 {
            self.mem.write_u32(paddr + i * 4, 0)
        }
    }

    #[allow(unused)]
    #[trusted]
    fn alloc_meta_page(&mut self) -> u32 {
        assert!(
            self.m_next < H_START,
            "Heap page allocation failed: out of memory"
        );
        let paddr = self.m_next;
        self.m_next += 1024;
        self.zero_page_out(paddr);
        paddr
    }

    #[allow(unused)]
    #[trusted]
    fn alloc_heap_page(&mut self) -> u32 {
        assert!(
            self.h_next < const { (2u64.pow(32) - 1024) as u32 },
            "Heap page allocation failed: out of memory"
        );
        let paddr = self.h_next;
        self.h_next += 1024;
        self.zero_page_out(paddr);
        paddr
    }

    #[allow(unused)]
    #[trusted]
    fn alloc(&mut self) -> u32 {
        let new_page_paddr = self.alloc_heap_page();
        for k in 0..64 {
            let t = self.mem.read_u32(k * 4);
            if t & 1 == 0 {
                // mid-level directory absent:
                let mid_paddr = self.alloc_meta_page(); // allocate a new mid-level directory page
                self.mem.write_u32(k * 4, mid_paddr | 1) // mark as Present and write to directory
            } else {
                let mid_paddr = (t >> 10) << 10; // otherwise, clear flags to get address

                for i in 0..0x100 {
                    // Same process for mid-level directory
                    let m = self.mem.read_u32(mid_paddr + i * 4);
                    let leaf_paddr;
                    if m & 1 == 0 {
                        leaf_paddr = self.alloc_meta_page();
                        self.mem.write_u32(mid_paddr + i * 4, leaf_paddr | 1);
                    } else {
                        leaf_paddr = (m >> 10) << 10;
                    }

                    for j in 0..0x100 {
                        // Same process for leaf page tables
                        let p = self.mem.read_u32(leaf_paddr + j * 4);
                        if p & 1 == 0 {
                            // free slot found: install the new page
                            self.mem.write_u32(leaf_paddr + j * 4, new_page_paddr | 1);
                            return (k << 26) | (i << 18) | (j << 10); // reconstruct vaddr
                        }
                    }
                }
            }
        }
        panic!("Page table full: no free virtual address")
    }
}
