include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "climc.mm"
include "co.mm"
include "wral.mm"
include "cc.mm"
include "wss.mm"
include "ccncf.mm"
include "cncfrss.mm"
include "syl.mm"
include "cncfrss2.mm"
include "ssid.mm"
include "cncfss.mm"
include "sylancl.mm"
include "sseldd.mm"
include "wf.mm"
include "cnlimc.mm"
include "simplbda.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem cnlimci
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let vx: setvar x
  assume cnlimci.f: |- ( ph -> F e. ( A -cn-> D ) )
  assume cnlimci.c: |- ( ph -> B e. A )


  assert |- ( ph -> ( F ` B ) e. ( F limCC B ) )

  proof
    wph
    cB
    cA
    wcel
    vx
    cv
    #
    cF
    cfv
    #
    cF
    @0
    climc
    co
    #
    wcel
    #
    vx
    cA
    wral
    #
    cB
    cF
    cfv
    #
    cF
    cB
    climc
    co
    #
    wcel
    #
    cnlimci.c
    wph
    cA
    cc
    wss
    #
    cF
    cA
    cc
    ccncf
    co
    #
    wcel
    #
    @4
    wph
    cF
    cA
    cD
    ccncf
    co
    #
    wcel
    #
    @8
    cnlimci.f
    cA
    cD
    cF
    cncfrss
    syl
    wph
    @11
    @9
    cF
    wph
    cD
    cc
    wss
    #
    cc
    cc
    wss
    @11
    @9
    wss
    wph
    @12
    @13
    cnlimci.f
    cA
    cD
    cF
    cncfrss2
    syl
    cc
    ssid
    cA
    cD
    cc
    cncfss
    sylancl
    cnlimci.f
    sseldd
    @8
    @10
    cA
    cc
    cF
    wf
    @4
    vx
    cA
    cF
    cnlimc
    simplbda
    syl2anc
    @3
    @7
    vx
    cB
    cA
    @0
    cB
    wceq
    @1
    @5
    @2
    @6
    @0
    cB
    cF
    fveq2
    @0
    cB
    cF
    climc
    oveq2
    eleq12d
    rspcv
    sylc
end
