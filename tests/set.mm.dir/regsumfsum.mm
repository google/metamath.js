include "ccnfld.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cr.mm"
include "cress.mm"
include "csu.mm"
include "cc.mm"
include "caddc.mm"
include "cvv.mm"
include "cfn.mm"
include "cc0.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "wcel.mm"
include "cnfldex.mm"
include "a1i.mm"
include "wss.mm"
include "ax-resscn.mm"
include "fmptd.mm"
include "0red.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "addid2d.mm"
include "addid1d.mm"
include "jca.mm"
include "gsumress.mm"
include "recnd.mm"
include "gsumfsum.mm"
include "eqtr3d.mm"

theorem regsumfsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  assume regsumfsum.1: |- ( ph -> A e. Fin )
  assume regsumfsum.2: |- ( ( ph /\ k e. A ) -> B e. RR )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint ph x
  assert |- ( ph -> ( ( CCfld |`s RR ) gsum ( k e. A |-> B ) ) = sum_ k e. A B )

  proof
    wph
    ccnfld
    vk
    cA
    cB
    cmpt
    #
    cgsu
    co
    ccnfld
    cr
    cress
    co
    #
    @0
    cgsu
    co
    cA
    cB
    vk
    csu
    wph
    vx
    cA
    cc
    caddc
    cr
    @0
    ccnfld
    @1
    cvv
    cfn
    cc0
    cnfldbas
    cnfldadd
    @1
    eqid
    ccnfld
    cvv
    wcel
    wph
    cnfldex
    a1i
    regsumfsum.1
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    wph
    vk
    cA
    cB
    cr
    @0
    regsumfsum.2
    @0
    eqid
    fmptd
    wph
    0red
    wph
    vx
    cv
    #
    cc
    wcel
    #
    wa
    #
    cc0
    @2
    caddc
    co
    @2
    wceq
    @2
    cc0
    caddc
    co
    @2
    wceq
    @4
    @2
    wph
    @3
    simpr
    #
    addid2d
    @4
    @2
    @5
    addid1d
    jca
    gsumress
    wph
    cA
    cB
    vk
    regsumfsum.1
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    regsumfsum.2
    recnd
    gsumfsum
    eqtr3d
end
