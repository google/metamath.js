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
include "smfpreimaltf.mm"
include "wceq.mm"
include "dmmptdf.mm"
include "nfdm.mm"
include "nfcv.mm"
include "rabeqf.mm"
include "syl.mm"
include "wa.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "breq1d.mm"
include "rabbida.mm"
include "eqidd.mm"
include "3eqtrrd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "mpbird.mm"

theorem smfpimltmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let vk: setvar k
  assume smfpimltmpt.x: |- F/ x ph
  assume smfpimltmpt.s: |- ( ph -> S e. SAlg )
  assume smfpimltmpt.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume smfpimltmpt.f: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfpimltmpt.r: |- ( ph -> R e. RR )

  disjoint A x
  disjoint R x
  disjoint k x
  assert |- ( ph -> { x e. A | B < R } e. ( S |`t A ) )

  proof
    wph
    cB
    cR
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
    cR
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
    cR
    @7
    cS
    @4
    vx
    cA
    cB
    nfmpt1
    #
    smfpimltmpt.s
    smfpimltmpt.f
    @7
    eqid
    smfpimltmpt.r
    smfpreimaltf
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
    smfpimltmpt.x
    @4
    eqid
    #
    smfpimltmpt.b
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
    smfpimltmpt.x
    wph
    @3
    cA
    wcel
    wa
    @5
    cB
    cR
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
    smfpimltmpt.b
    fvmpt2d
    breq1d
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
