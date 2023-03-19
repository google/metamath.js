include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "hlomcmat.mm"
include "atlrelat1.mm"
include "syl3an1.mm"

theorem hlrelat1
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlrelat1.b: |- B = ( Base ` K )
  assume hlrelat1.l: |- .<_ = ( le ` K )
  assume hlrelat1.s: |- .< = ( lt ` K )
  assume hlrelat1.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( X .< Y -> E. p e. A ( -. p .<_ X /\ p .<_ Y ) ) )

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
    c.lt
    wbr
    vp
    cv
    #
    cX
    c.le
    wbr
    wn
    @0
    cY
    c.le
    wbr
    wa
    vp
    cA
    wrex
    wi
    cK
    hlomcmat
    cA
    cB
    c.lt
    cK
    c.le
    cX
    cY
    vp
    hlrelat1.b
    hlrelat1.l
    hlrelat1.s
    hlrelat1.a
    atlrelat1
    syl3an1
end
