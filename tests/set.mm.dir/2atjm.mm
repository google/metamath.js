include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "wb.mm"
include "simp1.mm"
include "hlatjcl.mm"
include "simp23.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "latmcom.mm"
include "wne.mm"
include "3jca.mm"
include "nbrne2.mm"
include "3ad2ant3.mm"
include "simp3r.mm"
include "latjcl.mm"
include "lattrd.mm"
include "cvrat3.mm"
include "imp.mm"
include "syl23anc.mm"
include "eqeltrd.mm"
include "atcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem 2atjm
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  assume 2atjm.b: |- B = ( Base ` K )
  assume 2atjm.l: |- .<_ = ( le ` K )
  assume 2atjm.j: |- .\/ = ( join ` K )
  assume 2atjm.m: |- ./\ = ( meet ` K )
  assume 2atjm.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ X e. B ) /\ ( P .<_ X /\ -. Q .<_ X ) ) -> ( ( P .\/ Q ) ./\ X ) = P )

  proof
    cK
    chlt
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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    cQ
    cX
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cP
    cQ
    c.or
    co
    #
    cX
    c.an
    co
    #
    @8
    cP
    @10
    c.le
    wbr
    #
    cP
    @10
    wceq
    #
    @8
    cP
    @9
    c.le
    wbr
    #
    @5
    @11
    @8
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @13
    @0
    @4
    @14
    @7
    cK
    hllat
    3ad2ant1
    #
    @8
    @1
    @15
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    cA
    cB
    cP
    cK
    2atjm.b
    2atjm.a
    atbase
    syl
    #
    @8
    @2
    @16
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    cA
    cB
    cQ
    cK
    2atjm.b
    2atjm.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    cP
    cQ
    2atjm.b
    2atjm.l
    2atjm.j
    latlej1
    syl3anc
    @0
    @4
    @5
    @6
    simp3l
    #
    @8
    @14
    @15
    @9
    cB
    wcel
    #
    @3
    @13
    @5
    wa
    @11
    wb
    @17
    @19
    @8
    @0
    @1
    @2
    @23
    @0
    @4
    @7
    simp1
    #
    @18
    @20
    cA
    cB
    c.or
    cK
    cP
    cQ
    2atjm.b
    2atjm.j
    2atjm.a
    hlatjcl
    syl3anc
    #
    @0
    @1
    @2
    @3
    @7
    simp23
    #
    cB
    cK
    c.le
    c.an
    cP
    @9
    cX
    2atjm.b
    2atjm.l
    2atjm.m
    latlem12
    syl13anc
    mpbi2and
    @8
    cK
    cal
    wcel
    #
    @1
    @10
    cA
    wcel
    @11
    @12
    wb
    @0
    @4
    @27
    @7
    cK
    hlatl
    3ad2ant1
    @18
    @8
    @10
    cX
    @9
    c.an
    co
    #
    cA
    @8
    @14
    @23
    @3
    @10
    @28
    wceq
    @17
    @25
    @26
    cB
    cK
    c.an
    @9
    cX
    2atjm.b
    2atjm.m
    latmcom
    syl3anc
    @8
    @0
    @3
    @1
    @2
    w3a
    #
    cP
    cQ
    wne
    #
    @6
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @28
    cA
    wcel
    #
    @24
    @8
    @3
    @1
    @2
    @26
    @18
    @20
    3jca
    @7
    @0
    @30
    @4
    cP
    cQ
    cX
    c.le
    nbrne2
    3ad2ant3
    @0
    @4
    @5
    @6
    simp3r
    @8
    cB
    cK
    c.le
    cP
    cX
    @31
    2atjm.b
    2atjm.l
    @17
    @19
    @26
    @8
    @14
    @3
    @16
    @31
    cB
    wcel
    @17
    @26
    @21
    cB
    c.or
    cK
    cX
    cQ
    2atjm.b
    2atjm.j
    latjcl
    syl3anc
    @22
    @8
    @14
    @3
    @16
    cX
    @31
    c.le
    wbr
    @17
    @26
    @21
    cB
    c.or
    cK
    c.le
    cX
    cQ
    2atjm.b
    2atjm.l
    2atjm.j
    latlej1
    syl3anc
    lattrd
    @0
    @29
    wa
    @30
    @6
    @32
    w3a
    @33
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    c.an
    cX
    2atjm.b
    2atjm.l
    2atjm.j
    2atjm.m
    2atjm.a
    cvrat3
    imp
    syl23anc
    eqeltrd
    cA
    cP
    @10
    cK
    c.le
    2atjm.l
    2atjm.a
    atcmp
    syl3anc
    mpbid
    eqcomd
end
