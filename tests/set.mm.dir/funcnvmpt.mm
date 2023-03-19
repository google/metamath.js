include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wceq.mm"
include "wrmo.mm"
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
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdm.mm"
include "wb.mm"
include "funmpt2.mm"
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
include "simpr.mm"
include "cmpt.mm"
include "fveq1i.mm"
include "fvmpt2f.mm"
include "syl5eq.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "biimpar.mm"
include "funbrfvb.mm"
include "sylancr.mm"
include "syl5bbr.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "3bitr4rd.mm"
include "mobid.mm"
include "df-rmo.mm"
include "syl6bbr.mm"
include "albidv.mm"

theorem funcnvmpt
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
  assert |- ( ph -> ( Fun `' F <-> A. y E* x e. A y = B ) )

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
    @3
    cB
    wceq
    #
    vx
    cA
    wrmo
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
    @11
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
    @10
    @5
    vy
    @9
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
    @8
    vy
    wph
    @5
    @2
    cA
    wcel
    #
    @7
    wa
    #
    vx
    wmo
    @8
    wph
    @4
    @13
    vx
    funcnvmpt.0
    wph
    @12
    @4
    wa
    @12
    @2
    cF
    cfv
    #
    @3
    wceq
    #
    wa
    #
    @13
    @4
    wph
    @4
    @12
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
    vx
    cA
    cB
    cF
    funcnvmpt.3
    funmpt2
    #
    @2
    @3
    cF
    funbrfv2b
    ax-mp
    wph
    @18
    @12
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
    @22
    vx
    cA
    wral
    cA
    @23
    wceq
    wph
    @22
    vx
    cA
    funcnvmpt.0
    wph
    @12
    @22
    wph
    @12
    wa
    #
    cB
    cV
    wcel
    #
    @22
    funcnvmpt.4
    cB
    cV
    elex
    syl
    ex
    ralrimi
    @22
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
    @12
    @7
    @4
    @24
    @3
    @14
    wceq
    #
    @7
    @4
    @24
    @14
    cB
    @3
    @24
    @12
    @25
    @14
    cB
    wceq
    wph
    @12
    simpr
    funcnvmpt.4
    @12
    @25
    wa
    @14
    @2
    vx
    cA
    cB
    cmpt
    #
    cfv
    cB
    @2
    cF
    @29
    funcnvmpt.3
    fveq1i
    vx
    cA
    cB
    cV
    funcnvmpt.1
    fvmpt2f
    syl5eq
    syl2anc
    eqeq2d
    @28
    @15
    @24
    @4
    @14
    @3
    eqcom
    @24
    @20
    @18
    @15
    @4
    wb
    @21
    wph
    @18
    @12
    @26
    biimpar
    @2
    @3
    cF
    funbrfvb
    sylancr
    syl5bbr
    bitr3d
    pm5.32da
    @27
    3bitr4rd
    mobid
    @7
    vx
    cA
    df-rmo
    syl6bbr
    albidv
    syl5bb
end
