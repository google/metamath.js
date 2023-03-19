include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "hlomcmat.mm"
include "atlatle.mm"
include "syl3an1.mm"

theorem hlatle
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
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> A. p e. A ( p .<_ X -> p .<_ Y ) ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    w3a
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.le
    wbr
    vp
    cv
    #
    cX
    c.le
    wbr
    @0
    cY
    c.le
    wbr
    wi
    vp
    cA
    wral
    wb
    cK
    hlomcmat
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
    atlatle
    syl3an1
end
