include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cfv.mm"
include "wceq.mm"
include "hlomcmat.mm"
include "atlatmstc.mm"
include "sylan.mm"

theorem hlatmstcOLDN
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume hlatmstc.b: |- B = ( Base ` K )
  assume hlatmstc.l: |- .<_ = ( le ` K )
  assume hlatmstc.u: |- U = ( lub ` K )
  assume hlatmstc.a: |- A = ( Atoms ` K )

  disjoint A y
  disjoint B y
  disjoint .<_ y
  disjoint X y
  assert |- ( ( K e. HL /\ X e. B ) -> ( U ` { y e. A | y .<_ X } ) = X )

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
    vy
    cv
    cX
    c.le
    wbr
    vy
    cA
    crab
    cU
    cfv
    cX
    wceq
    cK
    hlomcmat
    vy
    cA
    cB
    cU
    cK
    c.le
    cX
    hlatmstc.b
    hlatmstc.l
    hlatmstc.u
    hlatmstc.a
    atlatmstc
    sylan
end
