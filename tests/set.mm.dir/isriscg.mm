include "cv.mm"
include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "crngiso.mm"
include "co.mm"
include "wex.mm"
include "crisc.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "exbidv.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "df-risc.mm"
include "brabg.mm"

theorem isriscg
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s

  disjoint R f
  disjoint S f
  disjoint R r
  disjoint R s
  disjoint r s
  disjoint f r
  disjoint f s
  disjoint S r
  disjoint S s
  assert |- ( ( R e. A /\ S e. B ) -> ( R ~=R S <-> ( ( R e. RingOps /\ S e. RingOps ) /\ E. f f e. ( R RngIso S ) ) ) )

  proof
    vr
    cv
    #
    crngo
    wcel
    #
    vs
    cv
    #
    crngo
    wcel
    #
    wa
    #
    vf
    cv
    #
    @0
    @2
    crngiso
    co
    #
    wcel
    #
    vf
    wex
    #
    wa
    cR
    crngo
    wcel
    #
    @3
    wa
    #
    @5
    cR
    @2
    crngiso
    co
    #
    wcel
    #
    vf
    wex
    #
    wa
    @9
    cS
    crngo
    wcel
    #
    wa
    #
    @5
    cR
    cS
    crngiso
    co
    #
    wcel
    #
    vf
    wex
    #
    wa
    vr
    vs
    cR
    cS
    cA
    cB
    crisc
    @0
    cR
    wceq
    #
    @4
    @10
    @8
    @13
    @19
    @1
    @9
    @3
    @0
    cR
    crngo
    eleq1
    anbi1d
    @19
    @7
    @12
    vf
    @19
    @6
    @11
    @5
    @0
    cR
    @2
    crngiso
    oveq1
    eleq2d
    exbidv
    anbi12d
    @2
    cS
    wceq
    #
    @10
    @15
    @13
    @18
    @20
    @3
    @14
    @9
    @2
    cS
    crngo
    eleq1
    anbi2d
    @20
    @12
    @17
    vf
    @20
    @11
    @16
    @5
    @2
    cS
    cR
    crngiso
    oveq2
    eleq2d
    exbidv
    anbi12d
    vf
    vs
    vr
    df-risc
    brabg
end
