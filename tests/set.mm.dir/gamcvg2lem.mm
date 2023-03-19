include "cn.mm"
include "cv.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "ce.mm"
include "cmpt.mm"
include "cmul.mm"
include "ccom.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "cfz.mm"
include "simpll.mm"
include "elfznn.mm"
include "cdiv.mm"
include "clog.mm"
include "cmin.mm"
include "wceq.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "cz.mm"
include "cdif.mm"
include "adantr.mm"
include "eldifad.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "dmgmdivn0.mm"
include "logcld.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "syl2anc.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "efadd.mm"
include "ccxp.mm"
include "efsub.mm"
include "divne0d.mm"
include "cxpefd.mm"
include "eqcomd.mm"
include "cc0.mm"
include "wne.mm"
include "eflog.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "seqhomo.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "eff.mm"
include "a1i.mm"
include "1z.mm"
include "serf.mm"
include "fcompt.mm"
include "wfn.mm"
include "seqfn.mm"
include "mp1i.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "dffn5.mm"
include "sylib.mm"

theorem gamcvg2lem
  let wph: wff ph
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  assume gamcvg2.f: |- F = ( m e. NN |-> ( ( ( ( m + 1 ) / m ) ^c A ) / ( ( A / m ) + 1 ) ) )
  assume gamcvg2.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )
  assume gamcvg2.g: |- G = ( m e. NN |-> ( ( A x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( A / m ) + 1 ) ) ) )

  disjoint A m
  disjoint m ph
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint k x
  disjoint G k
  disjoint n x
  disjoint G n
  disjoint G x
  disjoint k m
  disjoint k ph
  disjoint m n
  disjoint m x
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( exp o. seq 1 ( + , G ) ) = seq 1 ( x. , F ) )

  proof
    wph
    vk
    cn
    vk
    cv
    #
    caddc
    cG
    c1
    cseq
    #
    cfv
    ce
    cfv
    #
    cmpt
    #
    vk
    cn
    @0
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cmpt
    #
    ce
    @1
    ccom
    #
    @4
    wph
    vk
    cn
    @2
    @5
    wph
    @0
    cn
    wcel
    #
    wa
    #
    vn
    vx
    caddc
    cmul
    cc
    cG
    cF
    ce
    c1
    @0
    vn
    cv
    #
    cc
    wcel
    vx
    cv
    #
    cc
    wcel
    wa
    #
    @10
    @11
    caddc
    co
    #
    cc
    wcel
    @9
    @10
    @11
    addcl
    adantl
    @9
    @10
    c1
    @0
    cfz
    co
    wcel
    #
    wa
    #
    wph
    @10
    cn
    wcel
    #
    @10
    cG
    cfv
    #
    cc
    wcel
    wph
    @8
    @14
    simpll
    #
    @14
    @16
    @9
    @10
    @0
    elfznn
    adantl
    #
    wph
    @16
    wa
    #
    @17
    cA
    @10
    c1
    caddc
    co
    #
    @10
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    @10
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cc
    @16
    @17
    @28
    wceq
    wph
    vm
    @10
    cA
    vm
    cv
    #
    c1
    caddc
    co
    #
    @29
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    @29
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    @28
    cn
    cG
    @29
    @10
    wceq
    #
    @33
    @24
    @36
    @27
    cmin
    @37
    @32
    @23
    cA
    cmul
    @37
    @31
    @22
    clog
    @37
    @30
    @21
    @29
    @10
    cdiv
    @29
    @10
    c1
    caddc
    oveq1
    @37
    id
    oveq12d
    #
    fveq2d
    oveq2d
    @37
    @35
    @26
    clog
    @37
    @34
    @25
    c1
    caddc
    @29
    @10
    cA
    cdiv
    oveq2
    oveq1d
    #
    fveq2d
    oveq12d
    gamcvg2.g
    @24
    @27
    cmin
    ovex
    fvmpt
    adantl
    #
    @20
    @24
    @27
    @20
    cA
    @23
    @20
    cA
    cc
    cz
    cn
    cdif
    #
    wph
    cA
    cc
    @41
    cdif
    wcel
    @16
    gamcvg2.a
    adantr
    #
    eldifad
    #
    @20
    @23
    @20
    @22
    @20
    @21
    @10
    @20
    @21
    @20
    @10
    wph
    @16
    simpr
    #
    peano2nnd
    #
    nnrpd
    @20
    @10
    @44
    nnrpd
    rpdivcld
    relogcld
    recnd
    mulcld
    #
    @20
    @26
    @20
    @25
    c1
    @20
    cA
    @10
    @43
    @20
    @10
    @44
    nncnd
    #
    @20
    @10
    @44
    nnne0d
    #
    divcld
    @20
    1cnd
    #
    addcld
    #
    @20
    cA
    @10
    @42
    @44
    dmgmdivn0
    #
    logcld
    #
    subcld
    eqeltrd
    #
    syl2anc
    @9
    @0
    cn
    c1
    cuz
    cfv
    #
    wph
    @8
    simpr
    nnuz
    syl6eleq
    @12
    @13
    ce
    cfv
    @10
    ce
    cfv
    @11
    ce
    cfv
    cmul
    co
    wceq
    @9
    @10
    @11
    efadd
    adantl
    @15
    wph
    @16
    @17
    ce
    cfv
    #
    @10
    cF
    cfv
    #
    wceq
    @18
    @19
    @20
    @28
    ce
    cfv
    #
    @22
    cA
    ccxp
    co
    #
    @26
    cdiv
    co
    #
    @55
    @56
    @20
    @57
    @24
    ce
    cfv
    #
    @27
    ce
    cfv
    #
    cdiv
    co
    #
    @59
    @20
    @24
    cc
    wcel
    @27
    cc
    wcel
    @57
    @62
    wceq
    @46
    @52
    @24
    @27
    efsub
    syl2anc
    @20
    @60
    @58
    @61
    @26
    cdiv
    @20
    @58
    @60
    @20
    @22
    cA
    @20
    @21
    @10
    @20
    @10
    c1
    @47
    @49
    addcld
    #
    @47
    @48
    divcld
    @20
    @21
    @10
    @63
    @47
    @20
    @21
    @45
    nnne0d
    @48
    divne0d
    @43
    cxpefd
    eqcomd
    @20
    @26
    cc
    wcel
    @26
    cc0
    wne
    @61
    @26
    wceq
    @50
    @51
    @26
    eflog
    syl2anc
    oveq12d
    eqtrd
    @20
    @17
    @28
    ce
    @40
    fveq2d
    @16
    @56
    @59
    wceq
    wph
    vm
    @10
    @31
    cA
    ccxp
    co
    #
    @35
    cdiv
    co
    @59
    cn
    cF
    @37
    @64
    @58
    @35
    @26
    cdiv
    @37
    @31
    @22
    cA
    ccxp
    @38
    oveq1d
    @39
    oveq12d
    gamcvg2.f
    @58
    @26
    cdiv
    ovex
    fvmpt
    adantl
    3eqtr4d
    syl2anc
    seqhomo
    mpteq2dva
    wph
    cc
    cc
    ce
    wf
    #
    cn
    cc
    @1
    wf
    @7
    @3
    wceq
    @65
    wph
    eff
    a1i
    wph
    vn
    cG
    c1
    cn
    nnuz
    c1
    cz
    wcel
    #
    wph
    1z
    a1i
    @53
    serf
    vk
    ce
    @1
    cn
    cc
    cc
    fcompt
    syl2anc
    wph
    @4
    cn
    wfn
    #
    @4
    @6
    wceq
    wph
    @4
    @54
    wfn
    #
    @67
    @66
    @68
    wph
    1z
    cmul
    cF
    c1
    seqfn
    mp1i
    cn
    @54
    @4
    nnuz
    fneq2i
    sylibr
    vk
    cn
    @4
    dffn5
    sylib
    3eqtr4d
end
