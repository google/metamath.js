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
include "breq2d.mm"
include "cbvrab.mm"
include "a1i.mm"
include "eqid.mm"
include "smfpimgtxr.mm"
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

theorem smfpimgtxrmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cL: class L
  let cV: class V
  let vy: setvar y
  let vk: setvar k
  assume smfpimgtxrmpt.x: |- F/ x ph
  assume smfpimgtxrmpt.s: |- ( ph -> S e. SAlg )
  assume smfpimgtxrmpt.b: |- ( ( ph /\ x e. A ) -> B e. V )
  assume smfpimgtxrmpt.f: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfpimgtxrmpt.l: |- ( ph -> L e. RR* )

  disjoint A x
  disjoint L x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint L y
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
    @8
    cL
    vy
    cv
    #
    @4
    cfv
    #
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
    cL
    @11
    clt
    vx
    cL
    nfcv
    vx
    clt
    nfcv
    vx
    @10
    @4
    @14
    vx
    @10
    nfcv
    nffv
    nfbr
    @3
    @10
    wceq
    @5
    @11
    cL
    clt
    @3
    @10
    @4
    fveq2
    breq2d
    cbvrab
    a1i
    wph
    vy
    cL
    @7
    cS
    @4
    vy
    @4
    nfcv
    smfpimgtxrmpt.s
    smfpimgtxrmpt.f
    @7
    eqid
    smfpimgtxrmpt.l
    smfpimgtxr
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
    smfpimgtxrmpt.x
    @4
    eqid
    #
    smfpimgtxrmpt.b
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
    smfpimgtxrmpt.x
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
    @17
    a1i
    smfpimgtxrmpt.b
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
    @18
    eqcomd
    oveq2d
    eleq12d
    mpbird
end
