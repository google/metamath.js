include "cesum.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "nfcv.mm"
include "nfv.mm"
include "disjdsct.mm"
include "esumc.mm"
include "eqid.mm"
include "rnmpt.mm"
include "esumeq1.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem esumrnmpt
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume esumrnmpt.0: |- F/_ k A
  assume esumrnmpt.1: |- ( y = B -> C = D )
  assume esumrnmpt.2: |- ( ph -> A e. V )
  assume esumrnmpt.3: |- ( ( ph /\ k e. A ) -> D e. ( 0 [,] +oo ) )
  assume esumrnmpt.4: |- ( ( ph /\ k e. A ) -> B e. ( W \ { (/) } ) )
  assume esumrnmpt.5: |- ( ph -> Disj_ k e. A B )

  disjoint A y
  disjoint B y
  disjoint C k
  disjoint D y
  disjoint W k
  disjoint k ph
  disjoint ph y
  disjoint k y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint ph z
  disjoint k z
  assert |- ( ph -> sum* y e. ran ( k e. A |-> B ) C = sum* k e. A D )

  proof
    wph
    cA
    cD
    vk
    cesum
    vz
    cv
    cB
    wceq
    vk
    cA
    wrex
    vz
    cab
    #
    cC
    vy
    cesum
    #
    vk
    cA
    cB
    cmpt
    #
    crn
    #
    cC
    vy
    cesum
    #
    wph
    vy
    vz
    cA
    cD
    cB
    cC
    vk
    cV
    cW
    c0
    csn
    cdif
    vk
    cC
    nfcv
    wph
    vk
    nfv
    #
    esumrnmpt.0
    esumrnmpt.1
    esumrnmpt.2
    wph
    vk
    cA
    cB
    cW
    @5
    esumrnmpt.0
    esumrnmpt.4
    esumrnmpt.5
    disjdsct
    esumrnmpt.3
    esumrnmpt.4
    esumc
    @3
    @0
    wceq
    @4
    @1
    wceq
    vk
    vz
    cA
    cB
    @2
    @2
    eqid
    rnmpt
    @3
    @0
    cC
    vy
    esumeq1
    ax-mp
    syl6reqr
end
