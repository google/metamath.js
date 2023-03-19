include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrel.mm"
include "relcnv.mm"
include "nfcv.mm"
include "nfcnv.mm"
include "dffun6f.mm"
include "mpbiran.mm"
include "vex.mm"
include "brcnv.mm"
include "mobii.mm"
include "albii.mm"
include "bitri.mm"
include "nfv.mm"
include "cfv.mm"
include "cdm.mm"
include "wb.mm"
include "cmpt.mm"
include "funmpt.mm"
include "funeqi.mm"
include "mpbir.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "cvv.mm"
include "crab.mm"
include "wral.mm"
include "elex.mm"
include "syl.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabid2f.mm"
include "sylibr.mm"
include "dmmpt.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bian1d.mm"
include "fveq1i.mm"
include "simpr.mm"
include "fvmpt2f.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "wi.mm"
include "biimpar.mm"
include "funbrfvb.mm"
include "sylancr.mm"
include "eqcom.mm"
include "bibi1i.mm"
include "imbi2i.mm"
include "mpbi.mm"
include "bitr3d.mm"
include "pm5.32d.mm"
include "3bitr4rd.mm"
include "mobid.mm"
include "albid.mm"

theorem funcnvmptOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vz: setvar z
  assume funcnvmpt.0: |- F/ x ph
  assume funcnvmpt.1: |- F/_ x A
  assume funcnvmpt.2: |- F/_ x F
  assume funcnvmpt.3: |- F = ( x e. A |-> B )
  assume funcnvmpt.4: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint x y
  disjoint F y
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( ph -> ( Fun `' F <-> A. y E* x ( x e. A /\ y = B ) ) )

  proof
    cF
    ccnv
    #
    wfun
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    #
    wph
    @2
    cA
    wcel
    #
    @3
    cB
    wceq
    #
    wa
    #
    vx
    wmo
    #
    vy
    wal
    @1
    @3
    @2
    @0
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    #
    @6
    @1
    @0
    wrel
    @13
    cF
    relcnv
    vy
    vx
    @0
    vy
    @0
    nfcv
    vx
    cF
    funcnvmpt.2
    nfcnv
    dffun6f
    mpbiran
    @12
    @5
    vy
    @11
    @4
    vx
    @3
    @2
    cF
    vy
    vex
    vx
    vex
    brcnv
    mobii
    albii
    bitri
    wph
    @5
    @10
    vy
    wph
    vy
    nfv
    wph
    @4
    @9
    vx
    funcnvmpt.0
    wph
    @7
    @4
    wa
    @7
    @2
    cF
    cfv
    #
    @3
    wceq
    #
    wa
    #
    @9
    @4
    wph
    @4
    @7
    @15
    @4
    @2
    cF
    cdm
    #
    wcel
    #
    @15
    wa
    #
    wph
    @16
    cF
    wfun
    #
    @4
    @19
    wb
    @20
    vx
    cA
    cB
    cmpt
    #
    wfun
    vx
    cA
    cB
    funmpt
    cF
    @21
    funcnvmpt.3
    funeqi
    mpbir
    #
    @2
    @3
    cF
    funbrfv2b
    ax-mp
    wph
    @18
    @7
    @15
    wph
    @17
    cA
    @2
    wph
    cA
    cB
    cvv
    wcel
    #
    vx
    cA
    crab
    #
    @17
    wph
    @23
    vx
    cA
    wral
    cA
    @24
    wceq
    wph
    @23
    vx
    cA
    funcnvmpt.0
    wph
    @7
    @23
    wph
    @7
    wa
    #
    cB
    cV
    wcel
    #
    @23
    funcnvmpt.4
    cB
    cV
    elex
    syl
    ex
    ralrimi
    @23
    vx
    cA
    funcnvmpt.1
    rabid2f
    sylibr
    vx
    cA
    cB
    cF
    funcnvmpt.3
    dmmpt
    syl6reqr
    eleq2d
    #
    anbi1d
    syl5bb
    #
    bian1d
    wph
    @7
    @8
    @4
    wph
    @7
    @8
    @4
    wb
    @25
    @3
    @14
    wceq
    #
    @8
    @4
    @25
    @14
    cB
    @3
    @25
    @14
    @2
    @21
    cfv
    #
    cB
    @2
    cF
    @21
    funcnvmpt.3
    fveq1i
    @25
    @7
    @26
    @30
    cB
    wceq
    wph
    @7
    simpr
    funcnvmpt.4
    vx
    cA
    cB
    cV
    funcnvmpt.1
    fvmpt2f
    syl2anc
    syl5eq
    eqeq2d
    @25
    @15
    @4
    wb
    #
    wi
    @25
    @29
    @4
    wb
    #
    wi
    @25
    @20
    @18
    @31
    @22
    wph
    @18
    @7
    @27
    biimpar
    @2
    @3
    cF
    funbrfvb
    sylancr
    @31
    @32
    @25
    @15
    @29
    @4
    @14
    @3
    eqcom
    bibi1i
    imbi2i
    mpbi
    bitr3d
    ex
    pm5.32d
    @28
    3bitr4rd
    mobid
    albid
    syl5bb
end
