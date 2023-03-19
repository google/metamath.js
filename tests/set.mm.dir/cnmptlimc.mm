include "cmpt.mm"
include "cfv.mm"
include "climc.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wral.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "cnlimci.mm"
include "eqeltrrd.mm"

theorem cnmptlimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let cY: class Y
  assume cnmptlimc.f: |- ( ph -> ( x e. A |-> X ) e. ( A -cn-> D ) )
  assume cnmptlimc.b: |- ( ph -> B e. A )
  assume cnmptlimc.1: |- ( x = B -> X = Y )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint Y x
  assert |- ( ph -> Y e. ( ( x e. A |-> X ) limCC B ) )

  proof
    wph
    cB
    vx
    cA
    cX
    cmpt
    #
    cfv
    #
    cY
    @0
    cB
    climc
    co
    wph
    cB
    cA
    wcel
    #
    cY
    cD
    wcel
    #
    @1
    cY
    wceq
    cnmptlimc.b
    wph
    @2
    cX
    cD
    wcel
    #
    vx
    cA
    wral
    #
    @3
    cnmptlimc.b
    wph
    cA
    cD
    @0
    wf
    #
    @5
    wph
    @0
    cA
    cD
    ccncf
    co
    wcel
    @6
    cnmptlimc.f
    cA
    cD
    @0
    cncff
    syl
    vx
    cA
    cD
    cX
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    @4
    @3
    vx
    cB
    cA
    vx
    cv
    cB
    wceq
    cX
    cY
    cD
    cnmptlimc.1
    eleq1d
    rspcv
    sylc
    vx
    cB
    cX
    cY
    cA
    cD
    @0
    cnmptlimc.1
    @7
    fvmptg
    syl2anc
    wph
    cA
    cB
    cD
    @0
    cnmptlimc.f
    cnmptlimc.b
    cnlimci
    eqeltrrd
end
