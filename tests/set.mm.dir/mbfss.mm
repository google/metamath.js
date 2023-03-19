include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cdif.mm"
include "cr.mm"
include "cv.mm"
include "wa.mm"
include "wo.mm"
include "cc.mm"
include "cun.mm"
include "elun.mm"
include "undif2.mm"
include "wss.mm"
include "wceq.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "mbfmptcl.mm"
include "cc0.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "jaodan.mm"
include "syldan.mm"
include "recld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cres.mm"
include "resmptd.mm"
include "ismbfcn2.mm"
include "mpbid.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "fveq2d.mm"
include "re0.mm"
include "syl6eq.mm"
include "mpteq2dva.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "cvol.mm"
include "cdm.mm"
include "mbfdm2.mm"
include "difmbl.mm"
include "syl2anc.mm"
include "mbfconst.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "mbfres2.mm"
include "imcld.mm"
include "simprd.mm"
include "im0.mm"
include "mpbir2and.mm"

theorem mbfss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume mbfss.1: |- ( ph -> A C_ B )
  assume mbfss.2: |- ( ph -> B e. dom vol )
  assume mbfss.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume mbfss.4: |- ( ( ph /\ x e. ( B \ A ) ) -> C = 0 )
  assume mbfss.5: |- ( ph -> ( x e. A |-> C ) e. MblFn )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( x e. B |-> C ) e. MblFn )

  proof
    wph
    vx
    cB
    cC
    cmpt
    cmbf
    wcel
    vx
    cB
    cC
    cre
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    vx
    cB
    cC
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    wph
    cB
    cA
    cB
    cA
    cdif
    #
    @1
    wph
    vx
    cB
    @0
    cr
    @1
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    cC
    wph
    @6
    @5
    cA
    wcel
    #
    @5
    @4
    wcel
    #
    wo
    #
    cC
    cc
    wcel
    #
    wph
    @10
    @6
    @10
    @5
    cA
    @4
    cun
    #
    wcel
    wph
    @6
    @5
    cA
    @4
    elun
    wph
    @12
    cB
    @5
    wph
    @12
    cA
    cB
    cun
    #
    cB
    cA
    cB
    undif2
    wph
    cA
    cB
    wss
    @13
    cB
    wceq
    mbfss.1
    cA
    cB
    ssequn1
    sylib
    syl5eq
    #
    eleq2d
    syl5bbr
    biimpar
    wph
    @8
    @11
    @9
    wph
    vx
    cA
    cC
    cV
    mbfss.5
    mbfss.3
    mbfmptcl
    #
    wph
    @9
    wa
    #
    cC
    cc0
    cc
    mbfss.4
    0cn
    syl6eqel
    jaodan
    syldan
    #
    recld
    @1
    eqid
    fmptd
    wph
    @1
    cA
    cres
    vx
    cA
    @0
    cmpt
    #
    cmbf
    wph
    vx
    cB
    cA
    @0
    mbfss.1
    resmptd
    wph
    @18
    cmbf
    wcel
    #
    vx
    cA
    @2
    cmpt
    #
    cmbf
    wcel
    #
    wph
    vx
    cA
    cC
    cmpt
    cmbf
    wcel
    @19
    @21
    wa
    mbfss.5
    wph
    vx
    cA
    cC
    @15
    ismbfcn2
    mpbid
    #
    simpld
    eqeltrd
    wph
    @1
    @4
    cres
    #
    vx
    @4
    cc0
    cmpt
    #
    cmbf
    wph
    @23
    vx
    @4
    @0
    cmpt
    #
    @24
    @4
    cB
    wss
    #
    @23
    @25
    wceq
    cB
    cA
    difss
    #
    vx
    cB
    @4
    @0
    resmpt
    ax-mp
    wph
    vx
    @4
    @0
    cc0
    @16
    @0
    cc0
    cre
    cfv
    cc0
    @16
    cC
    cc0
    cre
    mbfss.4
    fveq2d
    re0
    syl6eq
    mpteq2dva
    syl5eq
    wph
    @24
    @4
    cc0
    csn
    cxp
    #
    cmbf
    vx
    @4
    cc0
    fconstmpt
    wph
    @4
    cvol
    cdm
    #
    wcel
    #
    cc0
    cc
    wcel
    @28
    cmbf
    wcel
    wph
    cB
    @29
    wcel
    cA
    @29
    wcel
    @30
    mbfss.2
    wph
    vx
    cA
    cC
    cV
    mbfss.5
    mbfss.3
    mbfdm2
    cB
    cA
    difmbl
    syl2anc
    0cn
    @4
    cc0
    mbfconst
    sylancl
    syl5eqelr
    #
    eqeltrd
    @14
    mbfres2
    wph
    cB
    cA
    @4
    @3
    wph
    vx
    cB
    @2
    cr
    @3
    @7
    cC
    @17
    imcld
    @3
    eqid
    fmptd
    wph
    @3
    cA
    cres
    @20
    cmbf
    wph
    vx
    cB
    cA
    @2
    mbfss.1
    resmptd
    wph
    @19
    @21
    @22
    simprd
    eqeltrd
    wph
    @3
    @4
    cres
    #
    @24
    cmbf
    wph
    @32
    vx
    @4
    @2
    cmpt
    #
    @24
    @26
    @32
    @33
    wceq
    @27
    vx
    cB
    @4
    @2
    resmpt
    ax-mp
    wph
    vx
    @4
    @2
    cc0
    @16
    @2
    cc0
    cim
    cfv
    cc0
    @16
    cC
    cc0
    cim
    mbfss.4
    fveq2d
    im0
    syl6eq
    mpteq2dva
    syl5eq
    @31
    eqeltrd
    @14
    mbfres2
    wph
    vx
    cB
    cC
    @17
    ismbfcn2
    mpbir2and
end
