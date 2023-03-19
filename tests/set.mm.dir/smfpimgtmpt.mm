include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cdm.mm"
include "nfmpt1.mm"
include "eqid.mm"
include "smfpreimagtf.mm"
include "wceq.mm"
include "dmmptdf.mm"
include "nfdm.mm"
include "nfcv.mm"
include "rabeqf.mm"
include "syl.mm"
include "wa.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "breq2d.mm"
include "rabbida.mm"
include "eqidd.mm"
include "3eqtrrd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "mpbird.mm"

theorem smfpimgtmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cL: class L
  let cV: class V
  let vk: setvar k
  assume smfpimgtmpt.x: |- F/ x ph
  assume smfpimgtmpt.s: |- ( ph -> S e. SAlg )
  assume smfpimgtmpt.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume smfpimgtmpt.f: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfpimgtmpt.l: |- ( ph -> L e. RR )

  disjoint A x
  disjoint L x
  disjoint k x
  assert |- ( ph -> { x e. A | L < B } e. ( S |`t A ) )

  proof
    wph
    cL
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cS
    cA
    crest
    co
    #
    wcel
    cL
    vx
    cv
    #
    vx
    cA
    cB
    cmpt
    #
    cfv
    #
    clt
    wbr
    #
    vx
    @4
    cdm
    #
    crab
    #
    cS
    @7
    crest
    co
    #
    wcel
    wph
    vx
    cL
    @7
    cS
    @4
    vx
    cA
    cB
    nfmpt1
    #
    smfpimgtmpt.s
    smfpimgtmpt.f
    @7
    eqid
    smfpimgtmpt.l
    smfpreimagtf
    wph
    @1
    @8
    @2
    @9
    wph
    @8
    @6
    vx
    cA
    crab
    #
    @1
    @1
    wph
    @7
    cA
    wceq
    @8
    @11
    wceq
    wph
    vx
    @4
    cA
    cB
    cV
    smfpimgtmpt.x
    @4
    eqid
    #
    smfpimgtmpt.b
    dmmptdf
    #
    @6
    vx
    @7
    cA
    vx
    @4
    @10
    nfdm
    vx
    cA
    nfcv
    rabeqf
    syl
    wph
    @6
    @0
    vx
    cA
    smfpimgtmpt.x
    wph
    @3
    cA
    wcel
    wa
    @5
    cB
    cL
    clt
    wph
    vx
    cA
    cB
    @4
    cV
    @4
    @4
    wceq
    wph
    @12
    a1i
    smfpimgtmpt.b
    fvmpt2d
    breq2d
    rabbida
    wph
    @1
    eqidd
    3eqtrrd
    wph
    cA
    @7
    cS
    crest
    wph
    @7
    cA
    @13
    eqcomd
    oveq2d
    eleq12d
    mpbird
end
