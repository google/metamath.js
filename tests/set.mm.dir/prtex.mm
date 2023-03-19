include "wprt.mm"
include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "wer.mm"
include "wb.mm"
include "prter1.mm"
include "erexb.mm"
include "syl.mm"
include "uniexb.mm"
include "syl6bbr.mm"

theorem prtex
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  assume prtlem18.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint p q
  disjoint p r
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint .~ p
  disjoint .~ v
  disjoint .~ w
  disjoint .~ z
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( Prt A -> ( .~ e. _V <-> A e. _V ) )

  proof
    cA
    wprt
    #
    c.sm
    cvv
    wcel
    #
    cA
    cuni
    #
    cvv
    wcel
    #
    cA
    cvv
    wcel
    @0
    @2
    c.sm
    wer
    @1
    @3
    wb
    vx
    vy
    vu
    cA
    c.sm
    prtlem18.1
    prter1
    @2
    c.sm
    erexb
    syl
    cA
    uniexb
    syl6bbr
end
