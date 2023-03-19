include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp22.mm"
include "atbase.mm"
include "syl.mm"
include "simp21.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simp23.mm"
include "wa.mm"
include "wb.mm"
include "latjcl.mm"
include "simp1.mm"
include "hlatjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "wne.mm"
include "simp3.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "lattrd.mm"
include "cvrat3.mm"
include "3impia.mm"
include "syl133anc.mm"
include "atcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem 2llnma1b
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  assume 2llnma1b.b: |- B = ( Base ` K )
  assume 2llnma1b.l: |- .<_ = ( le ` K )
  assume 2llnma1b.j: |- .\/ = ( join ` K )
  assume 2llnma1b.m: |- ./\ = ( meet ` K )
  assume 2llnma1b.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) /\ -. Q .<_ ( P .\/ X ) ) -> ( ( P .\/ X ) ./\ ( P .\/ Q ) ) = P )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cQ
    cP
    cX
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cP
    @5
    cP
    cQ
    c.or
    co
    #
    c.an
    co
    #
    @7
    cP
    @9
    c.le
    wbr
    #
    cP
    @9
    wceq
    #
    @7
    cP
    @5
    c.le
    wbr
    #
    cP
    @8
    c.le
    wbr
    #
    @10
    @7
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @1
    @12
    @0
    @4
    @14
    @6
    cK
    hllat
    3ad2ant1
    #
    @7
    @2
    @15
    @0
    @1
    @2
    @3
    @6
    simp22
    #
    cA
    cB
    cP
    cK
    2llnma1b.b
    2llnma1b.a
    atbase
    syl
    #
    @0
    @1
    @2
    @3
    @6
    simp21
    #
    cB
    c.or
    cK
    c.le
    cP
    cX
    2llnma1b.b
    2llnma1b.l
    2llnma1b.j
    latlej1
    syl3anc
    #
    @7
    @14
    @15
    cQ
    cB
    wcel
    #
    @13
    @16
    @18
    @7
    @3
    @21
    @0
    @1
    @2
    @3
    @6
    simp23
    #
    cA
    cB
    cQ
    cK
    2llnma1b.b
    2llnma1b.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    cP
    cQ
    2llnma1b.b
    2llnma1b.l
    2llnma1b.j
    latlej1
    syl3anc
    @7
    @14
    @15
    @5
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @12
    @13
    wa
    @10
    wb
    @16
    @18
    @7
    @14
    @15
    @1
    @24
    @16
    @18
    @19
    cB
    c.or
    cK
    cP
    cX
    2llnma1b.b
    2llnma1b.j
    latjcl
    syl3anc
    #
    @7
    @0
    @2
    @3
    @25
    @0
    @4
    @6
    simp1
    #
    @17
    @22
    cA
    cB
    c.or
    cK
    cP
    cQ
    2llnma1b.b
    2llnma1b.j
    2llnma1b.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    cP
    @5
    @8
    2llnma1b.b
    2llnma1b.l
    2llnma1b.m
    latlem12
    syl13anc
    mpbi2and
    @7
    cK
    cal
    wcel
    #
    @2
    @9
    cA
    wcel
    #
    @10
    @11
    wb
    @0
    @4
    @28
    @6
    cK
    hlatl
    3ad2ant1
    @17
    @7
    @0
    @24
    @2
    @3
    cP
    cQ
    wne
    #
    @6
    cP
    @5
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @29
    @27
    @26
    @17
    @22
    @7
    @12
    @6
    @30
    @20
    @0
    @4
    @6
    simp3
    #
    cP
    cQ
    @5
    c.le
    nbrne2
    syl2anc
    @33
    @7
    cB
    cK
    c.le
    cP
    @5
    @31
    2llnma1b.b
    2llnma1b.l
    @16
    @18
    @26
    @7
    @14
    @24
    @21
    @31
    cB
    wcel
    @16
    @26
    @23
    cB
    c.or
    cK
    @5
    cQ
    2llnma1b.b
    2llnma1b.j
    latjcl
    syl3anc
    @20
    @7
    @14
    @24
    @21
    @5
    @31
    c.le
    wbr
    @16
    @26
    @23
    cB
    c.or
    cK
    c.le
    @5
    cQ
    2llnma1b.b
    2llnma1b.l
    2llnma1b.j
    latlej1
    syl3anc
    lattrd
    @0
    @24
    @2
    @3
    w3a
    @30
    @6
    @32
    w3a
    @29
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    c.an
    @5
    2llnma1b.b
    2llnma1b.l
    2llnma1b.j
    2llnma1b.m
    2llnma1b.a
    cvrat3
    3impia
    syl133anc
    cA
    cP
    @9
    cK
    c.le
    2llnma1b.l
    2llnma1b.a
    atcmp
    syl3anc
    mpbid
    eqcomd
end
