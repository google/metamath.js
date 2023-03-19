include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "wceq.mm"
include "subgsubm.mm"
include "submod.mm"
include "sylan.mm"

theorem subgod
  let cA: class A
  let cP: class P
  let cG: class G
  let cH: class H
  let cO: class O
  let cY: class Y
  let vx: setvar x
  assume submod.h: |- H = ( G |`s Y )
  assume submod.o: |- O = ( od ` G )
  assume submod.p: |- P = ( od ` H )


  assert |- ( ( Y e. ( SubGrp ` G ) /\ A e. Y ) -> ( O ` A ) = ( P ` A ) )

  proof
    cY
    cG
    csubg
    cfv
    wcel
    cY
    cG
    csubmnd
    cfv
    wcel
    cA
    cY
    wcel
    cA
    cO
    cfv
    cA
    cP
    cfv
    wceq
    cY
    cG
    subgsubm
    cA
    cP
    cG
    cH
    cO
    cY
    submod.h
    submod.o
    submod.p
    submod
    sylan
end
