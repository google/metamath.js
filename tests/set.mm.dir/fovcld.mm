include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "3simpc.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "ffnov.mm"
include "simprbi.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "sylc.mm"

theorem fovcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume fovcld.1: |- ( ph -> F : ( R X. S ) --> C )


  assert |- ( ( ph /\ A e. R /\ B e. S ) -> ( A F B ) e. C )

  proof
    wph
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    @0
    @1
    wa
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cC
    wcel
    #
    vy
    cS
    wral
    vx
    cR
    wral
    #
    cA
    cB
    cF
    co
    #
    cC
    wcel
    #
    wph
    @0
    @1
    3simpc
    wph
    @0
    @6
    @1
    wph
    cR
    cS
    cxp
    #
    cC
    cF
    wf
    #
    @6
    fovcld.1
    @10
    cF
    @9
    wfn
    @6
    vx
    vy
    cR
    cS
    cC
    cF
    ffnov
    simprbi
    syl
    3ad2ant1
    @5
    @8
    cA
    @3
    cF
    co
    #
    cC
    wcel
    vx
    vy
    cA
    cB
    cR
    cS
    @2
    cA
    wceq
    @4
    @11
    cC
    @2
    cA
    @3
    cF
    oveq1
    eleq1d
    @3
    cB
    wceq
    @11
    @7
    cC
    @3
    cB
    cA
    cF
    oveq2
    eleq1d
    rspc2v
    sylc
end
