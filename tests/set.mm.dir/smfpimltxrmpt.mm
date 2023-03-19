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
include "wceq.mm"
include "nfmpt1.mm"
include "nfdm.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "eqid.mm"
include "smfpimltxr.mm"
include "eqeltrd.mm"
include "dmmptdf.mm"
include "rabeqf.mm"
include "syl.mm"
include "wa.mm"
include "fvmpt2d.mm"
include "rabbida.mm"
include "eqidd.mm"
include "3eqtrrd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "mpbird.mm"

theorem smfpimltxrmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume smfpimltxrmpt.x: |- F/ x ph
  assume smfpimltxrmpt.s: |- ( ph -> S e. SAlg )
  assume smfpimltxrmpt.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume smfpimltxrmpt.f: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfpimltxrmpt.r: |- ( ph -> R e. RR* )

  disjoint A x
  disjoint R x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint R y
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
    @8
    vy
    cv
    #
    @4
    cfv
    #
    cR
    clt
    wbr
    #
    vy
    @7
    crab
    #
    @9
    @8
    @13
    wceq
    wph
    @6
    @12
    vx
    vy
    @7
    vx
    @4
    vx
    cA
    cB
    nfmpt1
    #
    nfdm
    #
    vy
    @7
    nfcv
    @6
    vy
    nfv
    vx
    @11
    cR
    clt
    vx
    @10
    @4
    @14
    vx
    @10
    nfcv
    nffv
    vx
    clt
    nfcv
    vx
    cR
    nfcv
    nfbr
    @3
    @10
    wceq
    @5
    @11
    cR
    clt
    @3
    @10
    @4
    fveq2
    breq1d
    cbvrab
    a1i
    wph
    vy
    cR
    @7
    cS
    @4
    vy
    @4
    nfcv
    smfpimltxrmpt.s
    smfpimltxrmpt.f
    @7
    eqid
    smfpimltxrmpt.r
    smfpimltxr
    eqeltrd
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
    @16
    wceq
    wph
    vx
    @4
    cA
    cB
    cV
    smfpimltxrmpt.x
    @4
    eqid
    #
    smfpimltxrmpt.b
    dmmptdf
    #
    @6
    vx
    @7
    cA
    @15
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
    smfpimltxrmpt.x
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
    @17
    a1i
    smfpimltxrmpt.b
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
    @18
    eqcomd
    oveq2d
    eleq12d
    mpbird
end
