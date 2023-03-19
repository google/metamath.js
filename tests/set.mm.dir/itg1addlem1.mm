include "cfn.mm"
include "wcel.mm"
include "cvol.mm"
include "cdm.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "wral.mm"
include "wdisj.mm"
include "ciun.mm"
include "csu.mm"
include "wceq.mm"
include "cv.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "adantrr.mm"
include "simprr.mm"
include "sseldd.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simprd.mm"
include "ralrimivva.mm"
include "invdisj.mm"
include "volfiniun.mm"
include "syl3anc.mm"

theorem itg1addlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume itg1addlem.1: |- ( ph -> F : X --> Y )
  assume itg1addlem.2: |- ( ph -> A e. Fin )
  assume itg1addlem.3: |- ( ( ph /\ k e. A ) -> B C_ ( `' F " { k } ) )
  assume itg1addlem.4: |- ( ( ph /\ k e. A ) -> B e. dom vol )
  assume itg1addlem.5: |- ( ( ph /\ k e. A ) -> ( vol ` B ) e. RR )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( vol ` U_ k e. A B ) = sum_ k e. A ( vol ` B ) )

  proof
    wph
    cA
    cfn
    wcel
    cB
    cvol
    cdm
    wcel
    #
    cB
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vk
    cA
    wral
    vk
    cA
    cB
    wdisj
    #
    vk
    cA
    cB
    ciun
    cvol
    cfv
    cA
    @1
    vk
    csu
    wceq
    itg1addlem.2
    wph
    @3
    vk
    cA
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    @0
    @2
    itg1addlem.4
    itg1addlem.5
    jca
    ralrimiva
    wph
    vx
    cv
    #
    cF
    cfv
    #
    @5
    wceq
    #
    vx
    cB
    wral
    vk
    cA
    wral
    @4
    wph
    @9
    vk
    vx
    cA
    cB
    wph
    @6
    @7
    cB
    wcel
    #
    wa
    #
    wa
    #
    @7
    cX
    wcel
    #
    @9
    @12
    @7
    cF
    ccnv
    @5
    csn
    cima
    #
    wcel
    #
    @13
    @9
    wa
    #
    @12
    cB
    @14
    @7
    wph
    @6
    cB
    @14
    wss
    @10
    itg1addlem.3
    adantrr
    wph
    @6
    @10
    simprr
    sseldd
    @12
    cF
    cX
    wfn
    #
    @15
    @16
    wb
    wph
    @17
    @11
    wph
    cX
    cY
    cF
    wf
    @17
    itg1addlem.1
    cX
    cY
    cF
    ffn
    syl
    adantr
    cX
    @5
    @7
    cF
    fniniseg
    syl
    mpbid
    simprd
    ralrimivva
    vk
    vx
    cA
    cB
    @8
    invdisj
    syl
    cA
    cB
    vk
    volfiniun
    syl3anc
end
