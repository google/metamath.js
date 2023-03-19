include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cc0.mm"
include "wceq.mm"
include "cmo.mm"
include "co.mm"
include "cif.mm"
include "df-ov.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "eucalgval2.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "ifeq12d.mm"
include "3eqtr4d.mm"

theorem eucalgval
  let vx: setvar x
  let vy: setvar y
  let cE: class E
  let cX: class X
  let cM: class M
  let cN: class N
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R z
  disjoint E z
  assert |- ( X e. ( NN0 X. NN0 ) -> ( E ` X ) = if ( ( 2nd ` X ) = 0 , X , <. ( 2nd ` X ) , ( mod ` X ) >. ) )

  proof
    cX
    cn0
    cn0
    cxp
    wcel
    #
    cX
    c1st
    cfv
    #
    cX
    c2nd
    cfv
    #
    cop
    #
    cE
    cfv
    #
    @2
    cc0
    wceq
    #
    @3
    @2
    @1
    @2
    cmo
    co
    #
    cop
    #
    cif
    #
    cX
    cE
    cfv
    @5
    cX
    @2
    cX
    cmo
    cfv
    #
    cop
    #
    cif
    @0
    @4
    @1
    @2
    cE
    co
    #
    @8
    @1
    @2
    cE
    df-ov
    @0
    @1
    cn0
    wcel
    @2
    cn0
    wcel
    @11
    @8
    wceq
    cX
    cn0
    cn0
    xp1st
    cX
    cn0
    cn0
    xp2nd
    vx
    vy
    cE
    @1
    @2
    eucalgval.1
    eucalgval2
    syl2anc
    syl5eqr
    @0
    cX
    @3
    cE
    cX
    cn0
    cn0
    1st2nd2
    #
    fveq2d
    @0
    @5
    cX
    @3
    @10
    @7
    @12
    @0
    @9
    @6
    @2
    @0
    @9
    @3
    cmo
    cfv
    @6
    @0
    cX
    @3
    cmo
    @12
    fveq2d
    @1
    @2
    cmo
    df-ov
    syl6eqr
    opeq2d
    ifeq12d
    3eqtr4d
end
