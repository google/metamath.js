include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cres.mm"
include "subgnm.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"

theorem subgnm2
  let cA: class A
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume subgngp.h: |- H = ( G |`s A )
  assume subgnm.n: |- N = ( norm ` G )
  assume subgnm.m: |- M = ( norm ` H )


  assert |- ( ( A e. ( SubGrp ` G ) /\ X e. A ) -> ( M ` X ) = ( N ` X ) )

  proof
    cA
    cG
    csubg
    cfv
    wcel
    #
    cX
    cA
    wcel
    cX
    cM
    cfv
    cX
    cN
    cA
    cres
    #
    cfv
    cX
    cN
    cfv
    @0
    cX
    cM
    @1
    cA
    cG
    cH
    cM
    cN
    subgngp.h
    subgnm.n
    subgnm.m
    subgnm
    fveq1d
    cX
    cA
    cN
    fvres
    sylan9eq
end
