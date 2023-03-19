include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wn.mm"
include "hlrelat1.mm"
include "imp.mm"
include "wb.mm"
include "clat.mm"
include "hllat.mm"
include "id.mm"
include "atbase.mm"
include "wne.mm"
include "cvv.mm"
include "ovexd.mm"
include "pltval.mm"
include "syl3an3.mm"
include "latlej1.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "wceq.mm"
include "latleeqj1.mm"
include "3com23.mm"
include "latjcom.mm"
include "eqeq1d.mm"
include "notbid.mm"
include "nesym.mm"
include "syl6bbr.mm"
include "syl3an.mm"
include "3expa.mm"
include "anbi1d.mm"
include "rexbidva.mm"
include "3adant3.mm"
include "adantr.mm"
include "mpbird.mm"

theorem hlrelat5N
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlrelat5.b: |- B = ( Base ` K )
  assume hlrelat5.l: |- .<_ = ( le ` K )
  assume hlrelat5.s: |- .< = ( lt ` K )
  assume hlrelat5.j: |- .\/ = ( join ` K )
  assume hlrelat5.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X .< Y ) -> E. p e. A ( X .< ( X .\/ p ) /\ p .<_ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    wa
    cX
    cX
    vp
    cv
    #
    c.or
    co
    #
    c.lt
    wbr
    #
    @5
    cY
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    @5
    cX
    c.le
    wbr
    #
    wn
    #
    @8
    wa
    #
    vp
    cA
    wrex
    #
    @3
    @4
    @14
    cA
    cB
    c.lt
    cK
    c.le
    cX
    cY
    vp
    hlrelat5.b
    hlrelat5.l
    hlrelat5.s
    hlrelat5.a
    hlrelat1
    imp
    @3
    @10
    @14
    wb
    #
    @4
    @0
    @1
    @15
    @2
    @0
    @1
    wa
    #
    @9
    @13
    vp
    cA
    @16
    @5
    cA
    wcel
    #
    wa
    @7
    @12
    @8
    @0
    @1
    @17
    @7
    @12
    wb
    #
    @0
    cK
    clat
    wcel
    #
    @1
    @1
    @17
    @5
    cB
    wcel
    #
    @18
    cK
    hllat
    @1
    id
    cA
    cB
    @5
    cK
    hlrelat5.b
    hlrelat5.a
    atbase
    @19
    @1
    @20
    w3a
    #
    @7
    cX
    @6
    wne
    #
    @12
    @21
    @7
    cX
    @6
    c.le
    wbr
    #
    @22
    wa
    #
    @22
    @20
    @19
    @1
    @6
    cvv
    wcel
    @7
    @24
    wb
    @20
    cX
    @5
    c.or
    ovexd
    clat
    cB
    cvv
    c.lt
    cK
    c.le
    cX
    @6
    hlrelat5.l
    hlrelat5.s
    pltval
    syl3an3
    @21
    @23
    @22
    cB
    c.or
    cK
    c.le
    cX
    @5
    hlrelat5.b
    hlrelat5.l
    hlrelat5.j
    latlej1
    biantrurd
    bitr4d
    @21
    @12
    @6
    cX
    wceq
    #
    wn
    @22
    @21
    @11
    @25
    @21
    @11
    @5
    cX
    c.or
    co
    #
    cX
    wceq
    #
    @25
    @19
    @20
    @1
    @11
    @27
    wb
    cB
    c.or
    cK
    c.le
    @5
    cX
    hlrelat5.b
    hlrelat5.l
    hlrelat5.j
    latleeqj1
    3com23
    @21
    @6
    @26
    cX
    cB
    c.or
    cK
    cX
    @5
    hlrelat5.b
    hlrelat5.j
    latjcom
    eqeq1d
    bitr4d
    notbid
    cX
    @6
    nesym
    syl6bbr
    bitr4d
    syl3an
    3expa
    anbi1d
    rexbidva
    3adant3
    adantr
    mpbird
end
