include "c0.mm"
include "cuni.mm"
include "cqs.mm"
include "wcel.mm"
include "wne.mm"
include "neirr.mm"
include "cdm.mm"
include "wceq.mm"
include "prtlem16.mm"
include "elqsn0.mm"
include "mpan.mm"
include "mto.mm"

theorem prtlem400
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume prtlem13.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u v
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint u w
  disjoint u z
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint .~ w
  disjoint .~ z
  assert |- -. (/) e. ( U. A /. .~ )

  proof
    c0
    cA
    cuni
    #
    c.sm
    cqs
    wcel
    #
    c0
    c0
    wne
    #
    c0
    neirr
    c.sm
    cdm
    @0
    wceq
    @1
    @2
    vx
    vy
    vu
    cA
    c.sm
    prtlem13.1
    prtlem16
    @0
    c0
    c.sm
    elqsn0
    mpan
    mto
end
