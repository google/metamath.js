include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "hlatle.mm"
include "3com23.mm"
include "anbi12d.mm"
include "ralbiim.mm"
include "syl6rbbr.mm"
include "clat.mm"
include "hllat.mm"
include "latasymb.mm"
include "syl3an1.mm"
include "bitrd.mm"

theorem hlateq
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlatle.b: |- B = ( Base ` K )
  assume hlatle.l: |- .<_ = ( le ` K )
  assume hlatle.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( A. p e. A ( p .<_ X <-> p .<_ Y ) <-> X = Y ) )

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
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    @4
    cY
    c.le
    wbr
    #
    wb
    vp
    cA
    wral
    #
    cX
    cY
    c.le
    wbr
    #
    cY
    cX
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    wceq
    #
    @3
    @10
    @5
    @6
    wi
    vp
    cA
    wral
    #
    @6
    @5
    wi
    vp
    cA
    wral
    #
    wa
    @7
    @3
    @8
    @12
    @9
    @13
    cA
    cB
    cK
    c.le
    cX
    cY
    vp
    hlatle.b
    hlatle.l
    hlatle.a
    hlatle
    @0
    @2
    @1
    @9
    @13
    wb
    cA
    cB
    cK
    c.le
    cY
    cX
    vp
    hlatle.b
    hlatle.l
    hlatle.a
    hlatle
    3com23
    anbi12d
    @5
    @6
    vp
    cA
    ralbiim
    syl6rbbr
    @0
    cK
    clat
    wcel
    @1
    @2
    @10
    @11
    wb
    cK
    hllat
    cB
    cK
    c.le
    cX
    cY
    hlatle.b
    hlatle.l
    latasymb
    syl3an1
    bitrd
end
