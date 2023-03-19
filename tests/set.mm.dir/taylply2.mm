include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cfa.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cidp.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "ccom.mm"
include "taylpfval.mm"
include "wa.mm"
include "simpr.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "cpm.mm"
include "cn0.mm"
include "wss.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "dvnbss.mm"
include "syl3anc.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "sseqtrd.mm"
include "recnprss.mm"
include "sstrd.mm"
include "sseldd.mm"
include "adantr.mm"
include "subcld.mm"
include "cid.mm"
include "cres.mm"
include "df-idp.mm"
include "mptresid.mm"
include "eqtr4i.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "eqidd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "elplyd.mm"
include "c1.mm"
include "cnfld1.mm"
include "subrg1cl.mm"
include "plyid.mm"
include "syl2anc.mm"
include "plyconst.mm"
include "csubg.mm"
include "caddc.mm"
include "subrgsubg.mm"
include "cnfldadd.mm"
include "subgcl.mm"
include "3expb.mm"
include "sylan.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "cneg.mm"
include "cminusg.mm"
include "ax-1cn.mm"
include "cnfldneg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "subginvcl.mm"
include "syl5eqelr.mm"
include "plysub.mm"
include "plyco.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "dgrco.mm"
include "ccnv.mm"
include "cima.mm"
include "w3a.mm"
include "plyremlem.mm"
include "simp2d.mm"
include "dgrcl.mm"
include "nn0cnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "elfznn0.mm"
include "adantl.mm"
include "dvnf.mm"
include "dvn2bss.mm"
include "ffvelrnd.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "dgrle.mm"
include "eqbrtrd.mm"
include "jca.mm"

theorem taylply2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume taylpfval.t: |- T = ( N ( S Tayl F ) B )
  assume taylply2.1: |- ( ph -> D e. ( SubRing ` CCfld ) )
  assume taylply2.2: |- ( ph -> B e. D )
  assume taylply2.3: |- ( ( ph /\ k e. ( 0 ... N ) ) -> ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) e. D )

  disjoint B k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint D k
  disjoint S k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X k
  disjoint X x
  assert |- ( ph -> ( T e. ( Poly ` D ) /\ ( deg ` T ) <_ N ) )

  proof
    wph
    cT
    cD
    cply
    cfv
    #
    wcel
    cT
    cdgr
    cfv
    #
    cN
    cle
    wbr
    wph
    cT
    vy
    cc
    cc0
    cN
    cfz
    co
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    @3
    cfa
    cfv
    #
    cdiv
    co
    #
    vy
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cidp
    cc
    cB
    csn
    #
    cxp
    #
    cmin
    cof
    co
    #
    ccom
    #
    @0
    wph
    cT
    vx
    cc
    @2
    @8
    vx
    cv
    #
    cB
    cmin
    co
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    @17
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylpfval.t
    taylpfval
    wph
    vx
    vy
    cc
    cc
    @19
    @12
    @22
    @16
    @13
    wph
    @18
    cc
    wcel
    #
    wa
    @18
    cB
    wph
    @23
    simpr
    #
    wph
    cB
    cc
    wcel
    #
    @23
    wph
    cN
    @4
    cfv
    cdm
    #
    cc
    cB
    wph
    @26
    cA
    cc
    wph
    @26
    cF
    cdm
    #
    cA
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    cN
    cn0
    wcel
    @26
    @27
    wss
    taylpfval.s
    wph
    cc
    cvv
    wcel
    #
    @29
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @30
    @31
    wph
    cnex
    a1i
    #
    taylpfval.s
    taylpfval.f
    taylpfval.a
    cc
    cS
    cA
    cF
    cvv
    @28
    elpm2r
    syl22anc
    #
    taylpfval.n
    cS
    cF
    cN
    dvnbss
    syl3anc
    wph
    @32
    @27
    cA
    wceq
    taylpfval.f
    cA
    cc
    cF
    fdm
    syl
    sseqtrd
    wph
    cA
    cS
    cc
    taylpfval.a
    wph
    @29
    cS
    cc
    wss
    taylpfval.s
    cS
    recnprss
    syl
    sstrd
    sstrd
    taylpfval.b
    sseldd
    #
    adantr
    #
    subcld
    wph
    vx
    cc
    @18
    cB
    cmin
    cidp
    @15
    cvv
    cc
    cc
    @33
    @24
    @36
    cidp
    vx
    cc
    @18
    cmpt
    #
    wceq
    wph
    cidp
    cid
    cc
    cres
    @37
    df-idp
    vx
    cc
    mptresid
    eqtr4i
    a1i
    @15
    vx
    cc
    cB
    cmpt
    wceq
    wph
    vx
    cc
    cB
    fconstmpt
    a1i
    offval2
    wph
    @13
    eqidd
    #
    @9
    @19
    wceq
    #
    @2
    @11
    @21
    vk
    @39
    @10
    @20
    @8
    cmul
    @9
    @19
    @3
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    fmptco
    eqtr4d
    #
    wph
    vu
    vv
    cD
    @13
    @16
    wph
    vy
    @8
    cD
    vk
    cN
    wph
    cD
    ccnfld
    csubrg
    cfv
    wcel
    #
    cD
    cc
    wss
    #
    taylply2.1
    cD
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    taylpfval.n
    taylply2.3
    elplyd
    #
    wph
    vu
    vv
    cD
    cidp
    @15
    wph
    @42
    c1
    cD
    wcel
    #
    cidp
    @0
    wcel
    @43
    wph
    @41
    @45
    taylply2.1
    cD
    ccnfld
    c1
    cnfld1
    subrg1cl
    syl
    #
    cD
    plyid
    syl2anc
    wph
    @42
    cB
    cD
    wcel
    @15
    @0
    wcel
    @43
    taylply2.2
    cB
    cD
    plyconst
    syl2anc
    wph
    cD
    ccnfld
    csubg
    cfv
    wcel
    #
    vu
    cv
    #
    cD
    wcel
    #
    vv
    cv
    #
    cD
    wcel
    #
    wa
    #
    @48
    @50
    caddc
    co
    cD
    wcel
    #
    wph
    @41
    @47
    taylply2.1
    cD
    ccnfld
    subrgsubg
    syl
    #
    @47
    @49
    @51
    @53
    caddc
    cD
    ccnfld
    @48
    @50
    cnfldadd
    subgcl
    3expb
    sylan
    #
    wph
    @41
    @52
    @48
    @50
    cmul
    co
    cD
    wcel
    #
    taylply2.1
    @41
    @49
    @51
    @56
    cD
    ccnfld
    cmul
    @48
    @50
    cnfldmul
    subrgmcl
    3expb
    sylan
    #
    wph
    c1
    cneg
    #
    c1
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    cD
    c1
    cc
    wcel
    @60
    @58
    wceq
    ax-1cn
    c1
    cnfldneg
    ax-mp
    wph
    @47
    @45
    @60
    cD
    wcel
    @54
    @46
    cD
    ccnfld
    @59
    c1
    @59
    eqid
    subginvcl
    syl2anc
    syl5eqelr
    plysub
    #
    @55
    @57
    plyco
    eqeltrd
    wph
    @1
    @13
    cdgr
    cfv
    #
    cN
    cle
    wph
    @1
    @17
    cdgr
    cfv
    @62
    @16
    cdgr
    cfv
    #
    cmul
    co
    #
    @62
    wph
    cT
    @17
    cdgr
    @40
    fveq2d
    wph
    cD
    @13
    @16
    @62
    @63
    @62
    eqid
    @63
    eqid
    @44
    @61
    dgrco
    wph
    @64
    @62
    c1
    cmul
    co
    @62
    wph
    @63
    c1
    @62
    cmul
    wph
    @16
    cc
    cply
    cfv
    wcel
    #
    @63
    c1
    wceq
    #
    @16
    ccnv
    cc0
    csn
    cima
    @14
    wceq
    #
    wph
    @25
    @65
    @66
    @67
    w3a
    @35
    cB
    @16
    @16
    eqid
    plyremlem
    syl
    simp2d
    oveq2d
    wph
    @62
    wph
    @62
    wph
    @13
    @0
    wcel
    @62
    cn0
    wcel
    @44
    cD
    @13
    dgrcl
    syl
    nn0cnd
    mulid1d
    eqtrd
    3eqtrd
    wph
    vy
    @8
    cD
    vk
    @13
    cN
    @44
    taylpfval.n
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @6
    @7
    @69
    @5
    cdm
    #
    cc
    cB
    @5
    @69
    @29
    @30
    @3
    cn0
    wcel
    #
    @70
    cc
    @5
    wf
    wph
    @29
    @68
    taylpfval.s
    adantr
    #
    wph
    @30
    @68
    @34
    adantr
    #
    @68
    @71
    wph
    @3
    cN
    elfznn0
    adantl
    #
    cS
    cF
    @3
    dvnf
    syl3anc
    @69
    @26
    @70
    cB
    @69
    @29
    @30
    @68
    @26
    @70
    wss
    @72
    @73
    wph
    @68
    simpr
    cS
    cF
    @3
    cN
    dvn2bss
    syl3anc
    wph
    cB
    @26
    wcel
    @68
    taylpfval.b
    adantr
    sseldd
    ffvelrnd
    @69
    @7
    @69
    @71
    @7
    cn
    wcel
    @74
    @3
    faccl
    syl
    #
    nncnd
    @69
    @7
    @75
    nnne0d
    divcld
    @38
    dgrle
    eqbrtrd
    jca
end
