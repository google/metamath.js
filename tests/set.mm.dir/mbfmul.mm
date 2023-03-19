include "cmul.mm"
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
include "cmin.mm"
include "elin.mm"
include "simplbi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simprbi.mm"
include "remuld.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "ovexd.mm"
include "cr.mm"
include "recld.mm"
include "offval2.mm"
include "imcld.mm"
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
include "mbfmullem.mm"
include "simprd.mm"
include "mbfsub.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "immuld.mm"
include "mbfadd.mm"
include "mulcld.mm"
include "mpbir2and.mm"

theorem mbfmul
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cQ: class Q
  assume mbfmul.1: |- ( ph -> F e. MblFn )
  assume mbfmul.2: |- ( ph -> G e. MblFn )


  assert |- ( ph -> ( F oF x. G ) e. MblFn )

  proof
    wph
    cF
    cG
    cmul
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
    cmul
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
    cmul
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
    mbfmul.1
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
    mbfmul.2
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
    mbfmul.1
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
    mbfmul.2
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
    vx
    @3
    @5
    cim
    cfv
    #
    cmpt
    #
    vx
    @3
    @6
    cim
    cfv
    #
    cmpt
    #
    @0
    co
    #
    cmin
    cof
    co
    #
    cmbf
    wph
    @23
    vx
    @3
    @26
    @28
    cmul
    co
    #
    @31
    @33
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    @36
    wph
    vx
    @3
    @22
    @39
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
    @40
    @12
    @40
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
    @40
    @15
    @40
    @20
    @21
    @42
    simprbi
    @2
    cc
    @4
    cG
    ffvelrn
    syl2an
    #
    remuld
    mpteq2dva
    wph
    vx
    @3
    @37
    @38
    cmin
    @30
    @35
    @9
    cvv
    cvv
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
    @41
    @26
    @28
    cmul
    ovexd
    @41
    @31
    @33
    cmul
    ovexd
    wph
    vx
    @3
    @26
    @28
    cmul
    @27
    @29
    @9
    cr
    cr
    @46
    @41
    @5
    @43
    recld
    #
    @41
    @6
    @44
    recld
    #
    wph
    @27
    eqidd
    #
    wph
    @29
    eqidd
    #
    offval2
    wph
    vx
    @3
    @31
    @33
    cmul
    @32
    @34
    @9
    cr
    cr
    @46
    @41
    @5
    @43
    imcld
    #
    @41
    @6
    @44
    imcld
    #
    wph
    @32
    eqidd
    #
    wph
    @34
    eqidd
    #
    offval2
    offval2
    eqtr4d
    wph
    @30
    @35
    wph
    @3
    @27
    @29
    wph
    @27
    cmbf
    wcel
    #
    @32
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
    @55
    @56
    wa
    wph
    @57
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
    @59
    @57
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
    @58
    cmbf
    wcel
    @45
    @59
    cmbf
    wcel
    wph
    cF
    @58
    cmbf
    wph
    vx
    @1
    cc
    cF
    @12
    feqmptd
    mbfmul.1
    eqeltrrd
    @46
    @3
    @58
    mbfres
    syl2anc
    syl5eqelr
    wph
    vx
    @3
    @5
    @43
    ismbfcn2
    mpbid
    #
    simpld
    #
    wph
    @29
    cmbf
    wcel
    #
    @34
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
    @62
    @63
    wa
    wph
    @64
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
    @66
    @64
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
    @65
    cmbf
    wcel
    @45
    @66
    cmbf
    wcel
    wph
    cG
    @65
    cmbf
    wph
    vx
    @2
    cc
    cG
    @15
    feqmptd
    mbfmul.2
    eqeltrrd
    @46
    @3
    @65
    mbfres
    syl2anc
    syl5eqelr
    wph
    vx
    @3
    @6
    @44
    ismbfcn2
    mpbid
    #
    simpld
    #
    wph
    vx
    @3
    @26
    cr
    @27
    @47
    @27
    eqid
    fmptd
    #
    wph
    vx
    @3
    @28
    cr
    @29
    @48
    @29
    eqid
    fmptd
    #
    mbfmullem
    wph
    @3
    @32
    @34
    wph
    @55
    @56
    @60
    simprd
    #
    wph
    @62
    @63
    @67
    simprd
    #
    wph
    vx
    @3
    @31
    cr
    @32
    @51
    @32
    eqid
    fmptd
    #
    wph
    vx
    @3
    @33
    cr
    @34
    @52
    @34
    eqid
    fmptd
    #
    mbfmullem
    mbfsub
    eqeltrd
    wph
    @25
    @27
    @34
    @0
    co
    #
    @32
    @29
    @0
    co
    #
    caddc
    cof
    co
    #
    cmbf
    wph
    @25
    vx
    @3
    @26
    @33
    cmul
    co
    #
    @31
    @28
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @77
    wph
    vx
    @3
    @24
    @80
    @41
    @5
    @6
    @43
    @44
    immuld
    mpteq2dva
    wph
    vx
    @3
    @78
    @79
    caddc
    @75
    @76
    @9
    cvv
    cvv
    @46
    @41
    @26
    @33
    cmul
    ovexd
    @41
    @31
    @28
    cmul
    ovexd
    wph
    vx
    @3
    @26
    @33
    cmul
    @27
    @34
    @9
    cr
    cr
    @46
    @47
    @52
    @49
    @54
    offval2
    wph
    vx
    @3
    @31
    @28
    cmul
    @32
    @29
    @9
    cr
    cr
    @46
    @51
    @48
    @53
    @50
    offval2
    offval2
    eqtr4d
    wph
    @75
    @76
    wph
    @3
    @27
    @34
    @61
    @72
    @69
    @74
    mbfmullem
    wph
    @3
    @32
    @29
    @71
    @68
    @73
    @70
    mbfmullem
    mbfadd
    eqeltrd
    wph
    vx
    @3
    @7
    @41
    @5
    @6
    @43
    @44
    mulcld
    ismbfcn2
    mpbir2and
    eqeltrd
end
