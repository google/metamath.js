include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmbf.mm"
include "cvol.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "wcel.mm"
include "mbff.mm"
include "syl.mm"
include "ffn.mm"
include "mbfdm.mm"
include "eqid.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "cre.mm"
include "cim.mm"
include "elin.mm"
include "simplbi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simprbi.mm"
include "readdd.mm"
include "mpteq2dva.mm"
include "cr.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "recld.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "mbfres.mm"
include "syl5eqelr.mm"
include "ismbfcn2.mm"
include "mpbid.mm"
include "simpld.mm"
include "inss2.mm"
include "fmptd.mm"
include "mbfaddlem.mm"
include "eqeltrd.mm"
include "imaddd.mm"
include "imcld.mm"
include "simprd.mm"
include "addcld.mm"
include "mpbir2and.mm"

theorem mbfadd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cA: class A
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mbfadd.1: |- ( ph -> F e. MblFn )
  assume mbfadd.2: |- ( ph -> G e. MblFn )


  assert |- ( ph -> ( F oF + G ) e. MblFn )

  proof
    wph
    cF
    cG
    caddc
    cof
    #
    co
    vx
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cmbf
    wph
    vx
    @1
    @2
    @5
    @6
    caddc
    @3
    cF
    cG
    cvol
    cdm
    #
    @9
    wph
    @1
    cc
    cF
    wf
    #
    cF
    @1
    wfn
    wph
    cF
    cmbf
    wcel
    #
    @10
    mbfadd.1
    cF
    mbff
    syl
    #
    @1
    cc
    cF
    ffn
    syl
    wph
    @2
    cc
    cG
    wf
    #
    cG
    @2
    wfn
    wph
    cG
    cmbf
    wcel
    #
    @13
    mbfadd.2
    cG
    mbff
    syl
    #
    @2
    cc
    cG
    ffn
    syl
    wph
    @11
    @1
    @9
    wcel
    #
    mbfadd.1
    cF
    mbfdm
    syl
    #
    wph
    @14
    @2
    @9
    wcel
    #
    mbfadd.2
    cG
    mbfdm
    syl
    #
    @3
    eqid
    wph
    @4
    @1
    wcel
    #
    wa
    @5
    eqidd
    wph
    @4
    @2
    wcel
    #
    wa
    @6
    eqidd
    offval
    wph
    @8
    cmbf
    wcel
    vx
    @3
    @7
    cre
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    vx
    @3
    @7
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    wph
    @23
    vx
    @3
    @5
    cre
    cfv
    #
    cmpt
    #
    vx
    @3
    @6
    cre
    cfv
    #
    cmpt
    #
    @0
    co
    #
    cmbf
    wph
    @23
    vx
    @3
    @26
    @28
    caddc
    co
    #
    cmpt
    @30
    wph
    vx
    @3
    @22
    @31
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @6
    wph
    @10
    @20
    @5
    cc
    wcel
    @32
    @12
    @32
    @20
    @21
    @4
    @1
    @2
    elin
    #
    simplbi
    @1
    cc
    @4
    cF
    ffvelrn
    syl2an
    #
    wph
    @13
    @21
    @6
    cc
    wcel
    @32
    @15
    @32
    @20
    @21
    @34
    simprbi
    @2
    cc
    @4
    cG
    ffvelrn
    syl2an
    #
    readdd
    mpteq2dva
    wph
    vx
    @3
    @26
    @28
    caddc
    @27
    @29
    @9
    cr
    cr
    wph
    @16
    @18
    @3
    @9
    wcel
    #
    @17
    @19
    @1
    @2
    inmbl
    syl2anc
    #
    @33
    @5
    @35
    recld
    #
    @33
    @6
    @36
    recld
    #
    wph
    @27
    eqidd
    wph
    @29
    eqidd
    offval2
    eqtr4d
    wph
    @3
    @27
    @29
    wph
    @27
    cmbf
    wcel
    #
    vx
    @3
    @5
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    #
    wph
    vx
    @3
    @5
    cmpt
    #
    cmbf
    wcel
    @41
    @44
    wa
    wph
    @45
    vx
    @1
    @5
    cmpt
    #
    @3
    cres
    #
    cmbf
    @3
    @1
    wss
    @47
    @45
    wceq
    @1
    @2
    inss1
    vx
    @1
    @3
    @5
    resmpt
    ax-mp
    wph
    @46
    cmbf
    wcel
    @37
    @47
    cmbf
    wcel
    wph
    cF
    @46
    cmbf
    wph
    vx
    @1
    cc
    cF
    @12
    feqmptd
    mbfadd.1
    eqeltrrd
    @38
    @3
    @46
    mbfres
    syl2anc
    syl5eqelr
    wph
    vx
    @3
    @5
    @35
    ismbfcn2
    mpbid
    #
    simpld
    wph
    @29
    cmbf
    wcel
    #
    vx
    @3
    @6
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    #
    wph
    vx
    @3
    @6
    cmpt
    #
    cmbf
    wcel
    @49
    @52
    wa
    wph
    @53
    vx
    @2
    @6
    cmpt
    #
    @3
    cres
    #
    cmbf
    @3
    @2
    wss
    @55
    @53
    wceq
    @1
    @2
    inss2
    vx
    @2
    @3
    @6
    resmpt
    ax-mp
    wph
    @54
    cmbf
    wcel
    @37
    @55
    cmbf
    wcel
    wph
    cG
    @54
    cmbf
    wph
    vx
    @2
    cc
    cG
    @15
    feqmptd
    mbfadd.2
    eqeltrrd
    @38
    @3
    @54
    mbfres
    syl2anc
    syl5eqelr
    wph
    vx
    @3
    @6
    @36
    ismbfcn2
    mpbid
    #
    simpld
    wph
    vx
    @3
    @26
    cr
    @27
    @39
    @27
    eqid
    fmptd
    wph
    vx
    @3
    @28
    cr
    @29
    @40
    @29
    eqid
    fmptd
    mbfaddlem
    eqeltrd
    wph
    @25
    @43
    @51
    @0
    co
    #
    cmbf
    wph
    @25
    vx
    @3
    @42
    @50
    caddc
    co
    #
    cmpt
    @57
    wph
    vx
    @3
    @24
    @58
    @33
    @5
    @6
    @35
    @36
    imaddd
    mpteq2dva
    wph
    vx
    @3
    @42
    @50
    caddc
    @43
    @51
    @9
    cr
    cr
    @38
    @33
    @5
    @35
    imcld
    #
    @33
    @6
    @36
    imcld
    #
    wph
    @43
    eqidd
    wph
    @51
    eqidd
    offval2
    eqtr4d
    wph
    @3
    @43
    @51
    wph
    @41
    @44
    @48
    simprd
    wph
    @49
    @52
    @56
    simprd
    wph
    vx
    @3
    @42
    cr
    @43
    @59
    @43
    eqid
    fmptd
    wph
    vx
    @3
    @50
    cr
    @51
    @60
    @51
    eqid
    fmptd
    mbfaddlem
    eqeltrd
    wph
    vx
    @3
    @7
    @33
    @5
    @6
    @35
    @36
    addcld
    ismbfcn2
    mpbir2and
    eqeltrd
end
