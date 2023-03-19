include "chil.mm"
include "cch.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cort.mm"
include "wss.mm"
include "csp.mm"
include "cc0.mm"
include "chj.mm"
include "cva.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wf.mm"
include "chst.mm"
include "w3a.mm"
include "ax-hilex.mm"
include "chex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "df-hst.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem ishst
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
  assert |- ( S e. CHStates <-> ( S : CH --> ~H /\ ( normh ` ( S ` ~H ) ) = 1 /\ A. x e. CH A. y e. CH ( x C_ ( _|_ ` y ) -> ( ( ( S ` x ) .ih ( S ` y ) ) = 0 /\ ( S ` ( x vH y ) ) = ( ( S ` x ) +h ( S ` y ) ) ) ) ) )

  proof
    cS
    chil
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
    cno
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
    cS
    cfv
    #
    @6
    cS
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    @5
    @6
    chj
    co
    #
    cS
    cfv
    #
    @8
    @9
    cva
    co
    #
    wceq
    #
    wa
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
    chil
    cS
    wf
    #
    @19
    wa
    cS
    chst
    wcel
    @20
    @4
    @18
    w3a
    @1
    @20
    @19
    chil
    cch
    cS
    ax-hilex
    chex
    elmap
    anbi1i
    chil
    vf
    cv
    #
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    @7
    @5
    @21
    cfv
    #
    @6
    @21
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    @12
    @21
    cfv
    #
    @25
    @26
    cva
    co
    #
    wceq
    #
    wa
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
    @19
    vf
    cS
    @0
    chst
    @21
    cS
    wceq
    #
    @24
    @4
    @34
    @18
    @35
    @23
    @3
    c1
    @35
    @22
    @2
    cno
    chil
    @21
    cS
    fveq1
    fveq2d
    eqeq1d
    @35
    @33
    @17
    vx
    vy
    cch
    cch
    @35
    @32
    @16
    @7
    @35
    @28
    @11
    @31
    @15
    @35
    @27
    @10
    cc0
    @35
    @25
    @8
    @26
    @9
    csp
    @5
    @21
    cS
    fveq1
    #
    @6
    @21
    cS
    fveq1
    #
    oveq12d
    eqeq1d
    @35
    @29
    @13
    @30
    @14
    @12
    @21
    cS
    fveq1
    @35
    @25
    @8
    @26
    @9
    cva
    @36
    @37
    oveq12d
    eqeq12d
    anbi12d
    imbi2d
    2ralbidv
    anbi12d
    vx
    vy
    vf
    df-hst
    elrab2
    @20
    @4
    @18
    3anass
    3bitr4i
end
