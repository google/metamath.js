include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cpo.mm"
include "wi.mm"
include "simp13.mm"
include "atlpos.mm"
include "syl.mm"
include "pltnle.mm"
include "ex.mm"
include "syld3an1.mm"
include "wral.mm"
include "iman.mm"
include "ancom.mm"
include "xchbinx.mm"
include "ralbii.mm"
include "wb.mm"
include "atlatle.mm"
include "3com23.mm"
include "biimprd.mm"
include "syl5bir.mm"
include "con3d.mm"
include "dfrex2.mm"
include "syl6ibr.mm"
include "syld.mm"

theorem atlrelat1
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume atlrelat1.b: |- B = ( Base ` K )
  assume atlrelat1.l: |- .<_ = ( le ` K )
  assume atlrelat1.s: |- .< = ( lt ` K )
  assume atlrelat1.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. AtLat ) /\ X e. B /\ Y e. B ) -> ( X .< Y -> E. p e. A ( -. p .<_ X /\ p .<_ Y ) ) )

  proof
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    cal
    wcel
    #
    w3a
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
    cY
    cX
    c.le
    wbr
    #
    wn
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    wn
    #
    @10
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
    cK
    cpo
    wcel
    #
    @4
    @3
    @5
    @7
    @9
    wi
    @6
    @2
    @16
    @0
    @1
    @2
    @4
    @5
    simp13
    cK
    atlpos
    syl
    @16
    @4
    @5
    w3a
    @7
    @9
    cB
    c.lt
    cK
    c.le
    cX
    cY
    atlrelat1.b
    atlrelat1.l
    atlrelat1.s
    pltnle
    ex
    syld3an1
    @6
    @9
    @14
    wn
    #
    vp
    cA
    wral
    #
    wn
    @15
    @6
    @18
    @8
    @18
    @13
    @11
    wi
    #
    vp
    cA
    wral
    #
    @6
    @8
    @19
    @17
    vp
    cA
    @19
    @13
    @12
    wa
    @14
    @13
    @11
    iman
    @13
    @12
    ancom
    xchbinx
    ralbii
    @6
    @8
    @20
    @3
    @5
    @4
    @8
    @20
    wb
    cA
    cB
    cK
    c.le
    cY
    cX
    vp
    atlrelat1.b
    atlrelat1.l
    atlrelat1.a
    atlatle
    3com23
    biimprd
    syl5bir
    con3d
    @14
    vp
    cA
    dfrex2
    syl6ibr
    syld
end
