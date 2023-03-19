include "cmpt.mm"
include "wf.mm"
include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wsb.mm"
include "sbimi.mm"
include "sban.mm"
include "sbf.mm"
include "clelsb3f.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "sbcel12.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "csbconstgf.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "3imtr3i.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmptf.mm"
include "fmpt.mm"
include "sylib.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem fmptdF
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  assume fmptdF.p: |- F/ x ph
  assume fmptdF.a: |- F/_ x A
  assume fmptdF.c: |- F/_ x C
  assume fmptdF.1: |- ( ( ph /\ x e. A ) -> B e. C )
  assume fmptdF.2: |- F = ( x e. A |-> B )


  assert |- ( ph -> F : A --> C )

  proof
    wph
    cA
    cC
    vx
    cA
    cB
    cmpt
    #
    wf
    #
    cA
    cC
    cF
    wf
    wph
    vx
    vy
    cv
    #
    cB
    csb
    #
    cC
    wcel
    #
    vy
    cA
    wral
    @1
    wph
    @4
    vy
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vx
    vy
    wsb
    #
    cB
    cC
    wcel
    #
    vx
    vy
    wsb
    #
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @4
    @6
    @8
    vx
    vy
    fmptdF.1
    sbimi
    @7
    wph
    vx
    vy
    wsb
    #
    @5
    vx
    vy
    wsb
    #
    wa
    @11
    wph
    @5
    vx
    vy
    sban
    @12
    wph
    @13
    @10
    wph
    vx
    vy
    fmptdF.p
    sbf
    vy
    vx
    cA
    fmptdF.a
    clelsb3f
    anbi12i
    bitri
    @9
    @8
    vx
    @2
    wsbc
    #
    @4
    @8
    vx
    vy
    sbsbc
    @14
    @3
    vx
    @2
    cC
    csb
    #
    wcel
    @4
    vx
    @2
    cB
    cC
    sbcel12
    @15
    cC
    @3
    @2
    cvv
    wcel
    @15
    cC
    wceq
    vy
    vex
    vx
    @2
    cC
    cvv
    fmptdF.c
    csbconstgf
    ax-mp
    eleq2i
    bitri
    bitri
    3imtr3i
    ralrimiva
    vy
    cA
    cC
    @3
    @0
    vx
    vy
    cA
    cB
    @3
    fmptdF.a
    vy
    cA
    nfcv
    vy
    cB
    nfcv
    vx
    @2
    cB
    nfcsb1v
    vx
    @2
    cB
    csbeq1a
    cbvmptf
    fmpt
    sylib
    cA
    cC
    cF
    @0
    fmptdF.2
    feq1i
    sylibr
end
