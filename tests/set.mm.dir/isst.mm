include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cch.mm"
include "cmap.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cort.mm"
include "wss.mm"
include "chj.mm"
include "caddc.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "cst.mm"
include "w3a.mm"
include "ovex.mm"
include "chex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "df-st.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem isst
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cA: class A
  let vf: setvar f
  let cB: class B

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint S f
  disjoint B y
  assert |- ( S e. States <-> ( S : CH --> ( 0 [,] 1 ) /\ ( S ` ~H ) = 1 /\ A. x e. CH A. y e. CH ( x C_ ( _|_ ` y ) -> ( S ` ( x vH y ) ) = ( ( S ` x ) + ( S ` y ) ) ) ) )

  proof
    cS
    cc0
    c1
    cicc
    co
    #
    cch
    cmap
    co
    #
    wcel
    #
    chil
    cS
    cfv
    #
    c1
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cort
    cfv
    wss
    #
    @5
    @6
    chj
    co
    #
    cS
    cfv
    #
    @5
    cS
    cfv
    #
    @6
    cS
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    wa
    #
    wa
    cch
    @0
    cS
    wf
    #
    @16
    wa
    cS
    cst
    wcel
    @17
    @4
    @15
    w3a
    @2
    @17
    @16
    @0
    cch
    cS
    cc0
    c1
    cicc
    ovex
    chex
    elmap
    anbi1i
    chil
    vf
    cv
    #
    cfv
    #
    c1
    wceq
    #
    @7
    @8
    @18
    cfv
    #
    @5
    @18
    cfv
    #
    @6
    @18
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    wa
    @16
    vf
    cS
    @1
    cst
    @18
    cS
    wceq
    #
    @20
    @4
    @27
    @15
    @28
    @19
    @3
    c1
    chil
    @18
    cS
    fveq1
    eqeq1d
    @28
    @26
    @14
    vx
    vy
    cch
    cch
    @28
    @25
    @13
    @7
    @28
    @21
    @9
    @24
    @12
    @8
    @18
    cS
    fveq1
    @28
    @22
    @10
    @23
    @11
    caddc
    @5
    @18
    cS
    fveq1
    @6
    @18
    cS
    fveq1
    oveq12d
    eqeq12d
    imbi2d
    2ralbidv
    anbi12d
    vx
    vy
    vf
    df-st
    elrab2
    @17
    @4
    @15
    3anass
    3bitr4i
end
