include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cop.mm"
include "cmo.mm"
include "co.mm"
include "cif.mm"
include "wa.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "opeq12.mm"
include "oveq12.mm"
include "opeq12d.mm"
include "ifbieq12d.mm"
include "opex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem eucalgval2
  let vx: setvar x
  let vy: setvar y
  let cE: class E
  let cM: class M
  let cN: class N
  let cX: class X
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R z
  disjoint E z
  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M E N ) = if ( N = 0 , <. M , N >. , <. N , ( M mod N ) >. ) )

  proof
    vx
    vy
    cM
    cN
    cn0
    cn0
    vy
    cv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    @0
    cop
    #
    @0
    @2
    @0
    cmo
    co
    #
    cop
    #
    cif
    cN
    cc0
    wceq
    #
    cM
    cN
    cop
    #
    cN
    cM
    cN
    cmo
    co
    #
    cop
    #
    cif
    cE
    @2
    cM
    wceq
    #
    @0
    cN
    wceq
    #
    wa
    #
    @1
    @6
    @3
    @5
    @7
    @9
    @12
    @0
    cN
    cc0
    @10
    @11
    simpr
    #
    eqeq1d
    @2
    @0
    cM
    cN
    opeq12
    @12
    @0
    cN
    @4
    @8
    @13
    @2
    cM
    @0
    cN
    cmo
    oveq12
    opeq12d
    ifbieq12d
    eucalgval.1
    @6
    @7
    @9
    cM
    cN
    opex
    cN
    @8
    opex
    ifex
    ovmpt2a
end
