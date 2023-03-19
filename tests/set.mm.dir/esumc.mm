include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cesum.mm"
include "cmpt.mm"
include "cvv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfmpt1.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "abrexexd.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wf1o.mm"
include "wral.mm"
include "ex.mm"
include "ralrimi.mm"
include "fnmptf.mm"
include "eqid.mm"
include "rnmpt.mm"
include "a1i.mm"
include "dff1o2.mm"
include "syl3anbrc.mm"
include "wa.mm"
include "cfv.mm"
include "simpr.mm"
include "fvmpt2f.mm"
include "syl2anc.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "reximi.mm"
include "sylbi.mm"
include "nfel.mm"
include "wi.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimd.mm"
include "imp.mm"
include "sylan2.mm"
include "esumf1o.mm"
include "eqcomd.mm"

theorem esumc
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let cW: class W
  assume esumc.0: |- F/_ k D
  assume esumc.1: |- F/ k ph
  assume esumc.2: |- F/_ k A
  assume esumc.3: |- ( y = C -> D = B )
  assume esumc.4: |- ( ph -> A e. V )
  assume esumc.5: |- ( ph -> Fun `' ( k e. A |-> C ) )
  assume esumc.6: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumc.7: |- ( ( ph /\ k e. A ) -> C e. W )

  disjoint k y
  disjoint k z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint C y
  disjoint C z
  disjoint ph y
  assert |- ( ph -> sum* k e. A B = sum* y e. { z | E. k e. A z = C } D )

  proof
    wph
    vz
    cv
    #
    cC
    wceq
    #
    vk
    cA
    wrex
    #
    vz
    cab
    #
    cD
    vy
    cesum
    cA
    cB
    vk
    cesum
    wph
    @3
    cD
    cA
    cB
    vy
    vk
    vk
    cA
    cC
    cmpt
    #
    cC
    cvv
    esumc.1
    esumc.0
    vy
    cB
    nfcv
    @2
    vk
    vz
    @1
    vk
    cA
    nfre1
    nfab
    esumc.2
    vk
    cA
    cC
    nfmpt1
    esumc.3
    wph
    vk
    vz
    cA
    cC
    esumc.2
    wph
    cA
    cV
    wcel
    cA
    cvv
    wcel
    esumc.4
    cA
    cV
    elex
    syl
    abrexexd
    wph
    @4
    cA
    wfn
    #
    @4
    ccnv
    wfun
    @4
    crn
    @3
    wceq
    #
    cA
    @3
    @4
    wf1o
    wph
    cC
    cW
    wcel
    #
    vk
    cA
    wral
    @5
    wph
    @7
    vk
    cA
    esumc.1
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @7
    esumc.7
    ex
    ralrimi
    vk
    cA
    cC
    cW
    esumc.2
    fnmptf
    syl
    esumc.5
    @6
    wph
    vk
    vz
    cA
    cC
    @4
    @4
    eqid
    rnmpt
    a1i
    cA
    @3
    @4
    dff1o2
    syl3anbrc
    wph
    @9
    wa
    #
    @9
    @7
    @8
    @4
    cfv
    cC
    wceq
    wph
    @9
    simpr
    esumc.7
    vk
    cA
    cC
    cW
    esumc.2
    fvmpt2f
    syl2anc
    vy
    cv
    #
    @3
    wcel
    #
    wph
    cD
    cB
    wceq
    #
    vk
    cA
    wrex
    #
    cD
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @12
    @11
    cC
    wceq
    #
    vk
    cA
    wrex
    #
    @14
    @2
    @18
    vz
    @11
    vy
    vex
    @0
    @11
    wceq
    @1
    @17
    vk
    cA
    @0
    @11
    cC
    eqeq1
    rexbidv
    elab
    @17
    @13
    vk
    cA
    esumc.3
    reximi
    sylbi
    wph
    @14
    @16
    wph
    @13
    @16
    vk
    cA
    esumc.1
    vk
    cD
    @15
    esumc.0
    vk
    @15
    nfcv
    nfel
    wph
    @9
    @13
    @16
    wi
    @10
    @16
    @13
    cB
    @15
    wcel
    esumc.6
    cD
    cB
    @15
    eleq1
    syl5ibrcom
    ex
    rexlimd
    imp
    sylan2
    esumf1o
    eqcomd
end
