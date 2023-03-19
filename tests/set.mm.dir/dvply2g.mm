include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cply.mm"
include "wa.mm"
include "cc.mm"
include "cdv.mm"
include "co.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "cv.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "ccoe.mm"
include "cmul.mm"
include "cmpt.mm"
include "cexp.mm"
include "csu.mm"
include "wf.mm"
include "plyf.mm"
include "adantl.mm"
include "feqmptd.mm"
include "cuz.mm"
include "wceq.mm"
include "simplr.mm"
include "cz.mm"
include "dgrcl.mm"
include "nn0zd.mm"
include "adantr.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "simpr.mm"
include "eqid.mm"
include "coeid3.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cmin.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "coef3.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "peano2nn0.mm"
include "syl.mm"
include "dvply1.mm"
include "wss.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "elfznn0.mm"
include "simpll.mm"
include "zsssubrg.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "cnfld0.mm"
include "subg0cl.mm"
include "coef2.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "sylan2.mm"
include "elplyd.mm"
include "eqeltrd.mm"

theorem dvply2g
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( S e. ( SubRing ` CCfld ) /\ F e. ( Poly ` S ) ) -> ( CC _D F ) e. ( Poly ` S ) )

  proof
    cS
    ccnfld
    csubrg
    cfv
    wcel
    #
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    wa
    #
    cc
    cF
    cdv
    co
    va
    cc
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vb
    cv
    #
    vc
    cn0
    vc
    cv
    #
    c1
    caddc
    co
    #
    @8
    cF
    ccoe
    cfv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    va
    cv
    #
    @6
    cexp
    co
    #
    cmul
    co
    #
    vb
    csu
    #
    cmpt
    #
    @1
    @3
    va
    @9
    @12
    vb
    cF
    @18
    @4
    c1
    caddc
    co
    #
    @3
    cF
    va
    cc
    @14
    cF
    cfv
    #
    cmpt
    va
    cc
    cc0
    @19
    cfz
    co
    @6
    @9
    cfv
    @15
    cmul
    co
    vb
    csu
    #
    cmpt
    @3
    va
    cc
    cc
    cF
    @2
    cc
    cc
    cF
    wf
    @0
    cS
    cF
    plyf
    adantl
    feqmptd
    @3
    va
    cc
    @20
    @21
    @3
    @14
    cc
    wcel
    #
    wa
    #
    @2
    @19
    @4
    cuz
    cfv
    #
    wcel
    #
    @22
    @20
    @21
    wceq
    @0
    @2
    @22
    simplr
    @23
    @4
    cz
    wcel
    #
    @4
    @24
    wcel
    @25
    @3
    @26
    @22
    @3
    @4
    @2
    @4
    cn0
    wcel
    #
    @0
    cS
    cF
    dgrcl
    adantl
    #
    nn0zd
    adantr
    @4
    uzid
    @4
    @4
    peano2uz
    3syl
    @3
    @22
    simpr
    @9
    cS
    vb
    cF
    @19
    @4
    @14
    @9
    eqid
    #
    @4
    eqid
    coeid3
    syl3anc
    mpteq2dva
    eqtrd
    @3
    va
    cc
    @17
    cc0
    @19
    c1
    cmin
    co
    #
    cfz
    co
    #
    @16
    vb
    csu
    @3
    @5
    @31
    @16
    vb
    @3
    @4
    @30
    cc0
    cfz
    @3
    @30
    @4
    @3
    @4
    cc
    wcel
    c1
    cc
    wcel
    @30
    @4
    wceq
    @3
    @4
    @28
    nn0cnd
    ax-1cn
    @4
    c1
    pncan
    sylancl
    eqcomd
    oveq2d
    sumeq1d
    mpteq2dv
    @2
    cn0
    cc
    @9
    wf
    @0
    @9
    cS
    cF
    @29
    coef3
    adantl
    vc
    vb
    cn0
    @11
    @6
    c1
    caddc
    co
    #
    @32
    @9
    cfv
    #
    cmul
    co
    @7
    @6
    wceq
    #
    @8
    @32
    @10
    @33
    cmul
    @7
    @6
    c1
    caddc
    oveq1
    #
    @34
    @8
    @32
    @9
    @35
    fveq2d
    oveq12d
    cbvmptv
    @3
    @27
    @19
    cn0
    wcel
    @28
    @4
    peano2nn0
    syl
    dvply1
    @3
    va
    @13
    cS
    vb
    @4
    @0
    cS
    cc
    wss
    @2
    cS
    cc
    ccnfld
    cnfldbas
    subrgss
    adantr
    @28
    @6
    @5
    wcel
    @3
    @6
    cn0
    wcel
    @13
    cS
    wcel
    @6
    @4
    elfznn0
    @3
    cn0
    cS
    @6
    @12
    @3
    vc
    cn0
    @11
    cS
    @12
    @3
    @7
    cn0
    wcel
    #
    wa
    #
    @0
    @8
    cS
    wcel
    @10
    cS
    wcel
    @11
    cS
    wcel
    @0
    @2
    @36
    simpll
    @37
    cz
    cS
    @8
    @0
    cz
    cS
    wss
    @2
    @36
    cS
    zsssubrg
    ad2antrr
    @37
    @8
    @36
    @8
    cn0
    wcel
    @3
    @7
    peano2nn0
    adantl
    #
    nn0zd
    sseldd
    @37
    cn0
    cS
    @8
    @9
    @37
    @2
    cc0
    cS
    wcel
    #
    cn0
    cS
    @9
    wf
    @0
    @2
    @36
    simplr
    @0
    @39
    @2
    @36
    @0
    cS
    ccnfld
    csubg
    cfv
    wcel
    @39
    cS
    ccnfld
    subrgsubg
    cS
    ccnfld
    cc0
    cnfld0
    subg0cl
    syl
    ad2antrr
    @9
    cS
    cF
    @29
    coef2
    syl2anc
    @38
    ffvelrnd
    cS
    ccnfld
    cmul
    @8
    @10
    cnfldmul
    subrgmcl
    syl3anc
    @12
    eqid
    fmptd
    ffvelrnda
    sylan2
    elplyd
    eqeltrd
end
