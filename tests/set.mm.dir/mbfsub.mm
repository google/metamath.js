include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cneg.mm"
include "caddc.mm"
include "cmbf.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "mbff.mm"
include "syl.mm"
include "elin.mm"
include "simplbi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simprbi.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "cvol.mm"
include "wfn.mm"
include "ffn.mm"
include "mbfdm.mm"
include "eqid.mm"
include "eqidd.mm"
include "offval.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "negcld.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "resmpt.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "mbfres.mm"
include "inss2.mm"
include "mbfneg.mm"
include "mbfadd.mm"
include "eqeltrd.mm"

theorem mbfsub
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cA: class A
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mbfadd.1: |- ( ph -> F e. MblFn )
  assume mbfadd.2: |- ( ph -> G e. MblFn )


  assert |- ( ph -> ( F oF - G ) e. MblFn )

  proof
    wph
    cF
    cG
    cmin
    cof
    co
    #
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
    cmpt
    #
    vx
    @3
    @4
    cG
    cfv
    #
    cneg
    #
    cmpt
    #
    caddc
    cof
    co
    #
    cmbf
    wph
    vx
    @3
    @5
    @7
    cmin
    co
    #
    cmpt
    vx
    @3
    @5
    @8
    caddc
    co
    #
    cmpt
    @0
    @10
    wph
    vx
    @3
    @11
    @12
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @12
    @11
    @14
    @5
    @7
    wph
    @1
    cc
    cF
    wf
    #
    @4
    @1
    wcel
    #
    @5
    cc
    wcel
    @13
    wph
    cF
    cmbf
    wcel
    #
    @15
    mbfadd.1
    cF
    mbff
    syl
    #
    @13
    @16
    @4
    @2
    wcel
    #
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
    @2
    cc
    cG
    wf
    #
    @19
    @7
    cc
    wcel
    @13
    wph
    cG
    cmbf
    wcel
    #
    @22
    mbfadd.2
    cG
    mbff
    syl
    #
    @13
    @16
    @19
    @20
    simprbi
    @2
    cc
    @4
    cG
    ffvelrn
    syl2an
    #
    negsubd
    eqcomd
    mpteq2dva
    wph
    vx
    @1
    @2
    @5
    @7
    cmin
    @3
    cF
    cG
    cvol
    cdm
    #
    @26
    wph
    @15
    cF
    @1
    wfn
    @18
    @1
    cc
    cF
    ffn
    syl
    wph
    @22
    cG
    @2
    wfn
    @24
    @2
    cc
    cG
    ffn
    syl
    wph
    @17
    @1
    @26
    wcel
    #
    mbfadd.1
    cF
    mbfdm
    syl
    #
    wph
    @23
    @2
    @26
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
    @16
    wa
    @5
    eqidd
    wph
    @19
    wa
    @7
    eqidd
    offval
    wph
    vx
    @3
    @5
    @8
    caddc
    @6
    @9
    @26
    cc
    cc
    wph
    @27
    @29
    @3
    @26
    wcel
    #
    @28
    @30
    @1
    @2
    inmbl
    syl2anc
    #
    @21
    @14
    @7
    @25
    negcld
    wph
    @6
    eqidd
    wph
    @9
    eqidd
    offval2
    3eqtr4d
    wph
    @6
    @9
    wph
    vx
    @1
    @5
    cmpt
    #
    @3
    cres
    #
    @6
    cmbf
    @3
    @1
    wss
    @34
    @6
    wceq
    wph
    @1
    @2
    inss1
    vx
    @1
    @3
    @5
    resmpt
    mp1i
    wph
    @33
    cmbf
    wcel
    @31
    @34
    cmbf
    wcel
    wph
    cF
    @33
    cmbf
    wph
    vx
    @1
    cc
    cF
    @18
    feqmptd
    mbfadd.1
    eqeltrrd
    @32
    @3
    @33
    mbfres
    syl2anc
    eqeltrrd
    wph
    vx
    @3
    @7
    cc
    @25
    wph
    vx
    @2
    @7
    cmpt
    #
    @3
    cres
    #
    vx
    @3
    @7
    cmpt
    #
    cmbf
    @3
    @2
    wss
    @36
    @37
    wceq
    wph
    @1
    @2
    inss2
    vx
    @2
    @3
    @7
    resmpt
    mp1i
    wph
    @35
    cmbf
    wcel
    @31
    @36
    cmbf
    wcel
    wph
    cG
    @35
    cmbf
    wph
    vx
    @2
    cc
    cG
    @24
    feqmptd
    mbfadd.2
    eqeltrrd
    @32
    @3
    @35
    mbfres
    syl2anc
    eqeltrrd
    mbfneg
    mbfadd
    eqeltrd
end
