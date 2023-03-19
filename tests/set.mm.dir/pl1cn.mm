include "cv.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cid.mm"
include "cres.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cmulr.mm"
include "ce1.mm"
include "crn.mm"
include "eqid.mm"
include "wa.mm"
include "w3a.mm"
include "cmpt.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvexd.mm"
include "cuni.mm"
include "wfn.mm"
include "wceq.mm"
include "simp1.mm"
include "wf.mm"
include "cnf.mm"
include "ffn.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "dffn5.mm"
include "ctopon.mm"
include "ctrg.mm"
include "ctgp.mm"
include "trgtgp.mm"
include "tgptopon.mm"
include "3syl.mm"
include "toponuni.mm"
include "fneq2d.mm"
include "syl5rbbr.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "3ad2ant3.mm"
include "offval2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqeltrrd.mm"
include "simp3.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cplusf.mm"
include "plusffval.mm"
include "tgpcn.mm"
include "syl5eqelr.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "eqeltrd.mm"
include "3adant2l.mm"
include "3adant3l.mm"
include "3expb.mm"
include "cmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "mulrcn.mm"
include "eleq1.mm"
include "adantr.mm"
include "simpr.mm"
include "cnconst2.mm"
include "syl3anc.mm"
include "idcn.mm"
include "ccrg.mm"
include "cpws.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "dffn3.mm"
include "biimpi.mm"
include "4syl.mm"
include "ffvelrnd.mm"
include "rneqi.mm"
include "syl6eleq.mm"
include "pf1ind.mm"

theorem pl1cn
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let vh: setvar h
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pl1cn.p: |- P = ( Poly1 ` R )
  assume pl1cn.e: |- E = ( eval1 ` R )
  assume pl1cn.b: |- B = ( Base ` P )
  assume pl1cn.k: |- K = ( Base ` R )
  assume pl1cn.j: |- J = ( TopOpen ` R )
  assume pl1cn.1: |- ( ph -> R e. CRing )
  assume pl1cn.2: |- ( ph -> R e. TopRing )
  assume pl1cn.3: |- ( ph -> F e. B )


  assert |- ( ph -> ( E ` F ) e. ( J Cn J ) )

  proof
    wph
    vh
    cv
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    cK
    vf
    cv
    #
    csn
    cxp
    #
    @1
    wcel
    #
    cid
    cK
    cres
    #
    @1
    wcel
    #
    @2
    @1
    wcel
    #
    vg
    cv
    #
    @1
    wcel
    #
    @2
    @8
    cR
    cplusg
    cfv
    #
    cof
    co
    #
    @1
    wcel
    #
    @2
    @8
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    @1
    wcel
    #
    cF
    cE
    cfv
    #
    @1
    wcel
    vh
    @16
    cK
    @10
    cR
    ce1
    cfv
    #
    crn
    #
    cR
    @13
    vf
    vg
    pl1cn.k
    @10
    eqid
    #
    @13
    eqid
    #
    @18
    eqid
    wph
    @2
    @18
    wcel
    #
    @7
    wa
    #
    @8
    @18
    wcel
    #
    @9
    wa
    #
    @12
    wph
    @22
    @9
    @12
    @23
    wph
    @7
    @9
    @12
    @21
    wph
    @7
    @9
    w3a
    #
    @11
    vx
    cK
    vx
    cv
    #
    @2
    cfv
    #
    @26
    @8
    cfv
    #
    @10
    co
    #
    cmpt
    @1
    @25
    vx
    cK
    @27
    @28
    @10
    @2
    @8
    cvv
    cvv
    cvv
    cK
    cvv
    wcel
    @25
    cK
    cR
    cbs
    cfv
    cvv
    pl1cn.k
    cR
    cbs
    fvex
    eqeltri
    a1i
    #
    @25
    @26
    cK
    wcel
    wa
    #
    @26
    @2
    fvexd
    #
    @31
    @26
    @8
    fvexd
    #
    @25
    wph
    @2
    cJ
    cuni
    #
    wfn
    #
    @2
    vx
    cK
    @27
    cmpt
    #
    wceq
    #
    wph
    @7
    @9
    simp1
    #
    @7
    wph
    @35
    @9
    @7
    @34
    @34
    @2
    wf
    @35
    @2
    cJ
    cJ
    @34
    @34
    @34
    eqid
    #
    @39
    cnf
    @34
    @34
    @2
    ffn
    syl
    3ad2ant2
    wph
    @35
    @37
    @37
    @2
    cK
    wfn
    wph
    @35
    vx
    cK
    @2
    dffn5
    wph
    cK
    @34
    @2
    wph
    cJ
    cK
    ctopon
    cfv
    wcel
    #
    cK
    @34
    wceq
    wph
    cR
    ctrg
    wcel
    #
    cR
    ctgp
    wcel
    #
    @40
    pl1cn.2
    cR
    trgtgp
    #
    cR
    cJ
    cK
    pl1cn.j
    pl1cn.k
    tgptopon
    3syl
    #
    cK
    cJ
    toponuni
    syl
    #
    fneq2d
    syl5rbbr
    biimpa
    syl2anc
    #
    @25
    wph
    @8
    @34
    wfn
    #
    @8
    vx
    cK
    @28
    cmpt
    #
    wceq
    #
    @38
    @9
    wph
    @47
    @7
    @9
    @34
    @34
    @8
    wf
    @47
    @8
    cJ
    cJ
    @34
    @34
    @39
    @39
    cnf
    @34
    @34
    @8
    ffn
    syl
    3ad2ant3
    wph
    @47
    @49
    @49
    @8
    cK
    wfn
    wph
    @47
    vx
    cK
    @8
    dffn5
    wph
    cK
    @34
    @8
    @45
    fneq2d
    syl5rbbr
    biimpa
    syl2anc
    #
    offval2
    @25
    vx
    vy
    vz
    @27
    @28
    vy
    cv
    #
    vz
    cv
    #
    @10
    co
    #
    @29
    cJ
    cJ
    cJ
    cJ
    cK
    cK
    cK
    wph
    @7
    @40
    @9
    @44
    3ad2ant1
    #
    @25
    @2
    @36
    @1
    @46
    wph
    @7
    @9
    simp2
    eqeltrrd
    #
    @25
    @8
    @48
    @1
    @50
    wph
    @7
    @9
    simp3
    eqeltrrd
    #
    @54
    @54
    wph
    @7
    vy
    vz
    cK
    cK
    @53
    cmpt2
    #
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    wcel
    @9
    wph
    @57
    cR
    cplusf
    cfv
    #
    @58
    vy
    vz
    cK
    @10
    @59
    cR
    pl1cn.k
    @19
    @59
    eqid
    #
    plusffval
    wph
    @41
    @42
    @59
    @58
    wcel
    pl1cn.2
    @43
    @59
    cR
    cJ
    pl1cn.j
    @60
    tgpcn
    3syl
    syl5eqelr
    3ad2ant1
    @51
    @27
    @52
    @28
    @10
    oveq12
    cnmpt12
    eqeltrd
    3adant2l
    3adant3l
    3expb
    wph
    @22
    @24
    @15
    wph
    @22
    @9
    @15
    @23
    wph
    @7
    @9
    @15
    @21
    @25
    @14
    vx
    cK
    @27
    @28
    @13
    co
    #
    cmpt
    @1
    @25
    vx
    cK
    @27
    @28
    @13
    @2
    @8
    cvv
    cvv
    cvv
    @30
    @32
    @33
    @46
    @50
    offval2
    @25
    vx
    vy
    vz
    @27
    @28
    @51
    @52
    @13
    co
    #
    @61
    cJ
    cJ
    cJ
    cJ
    cK
    cK
    cK
    @54
    @55
    @56
    @54
    @54
    wph
    @7
    vy
    vz
    cK
    cK
    @62
    cmpt2
    #
    @58
    wcel
    @9
    wph
    @63
    cR
    cmgp
    cfv
    #
    cplusf
    cfv
    #
    @58
    vy
    vz
    cK
    @13
    @65
    @64
    cK
    cR
    @64
    @64
    eqid
    #
    pl1cn.k
    mgpbas
    cR
    @13
    @64
    @66
    @20
    mgpplusg
    @65
    eqid
    #
    plusffval
    wph
    @41
    @65
    @58
    wcel
    pl1cn.2
    cR
    @65
    cJ
    pl1cn.j
    @67
    mulrcn
    syl
    syl5eqelr
    3ad2ant1
    @51
    @27
    @52
    @28
    @13
    oveq12
    cnmpt12
    eqeltrd
    3adant2l
    3adant3l
    3expb
    @0
    @3
    @1
    eleq1
    @0
    @5
    @1
    eleq1
    @0
    @2
    @1
    eleq1
    @0
    @8
    @1
    eleq1
    @0
    @11
    @1
    eleq1
    @0
    @14
    @1
    eleq1
    @0
    @16
    @1
    eleq1
    wph
    @2
    cK
    wcel
    #
    wa
    @40
    @40
    @68
    @4
    wph
    @40
    @68
    @44
    adantr
    #
    @69
    wph
    @68
    simpr
    @2
    cJ
    cJ
    cK
    cK
    cnconst2
    syl3anc
    wph
    @40
    @6
    @44
    cJ
    cK
    idcn
    syl
    wph
    @16
    cE
    crn
    #
    @18
    wph
    cB
    @70
    cF
    cE
    wph
    cR
    ccrg
    wcel
    #
    cB
    @70
    cE
    wf
    #
    pl1cn.1
    @71
    cE
    cP
    cR
    cK
    cpws
    co
    #
    crh
    co
    wcel
    cB
    @73
    cbs
    cfv
    #
    cE
    wf
    cE
    cB
    wfn
    #
    @72
    cK
    cP
    cR
    @73
    cE
    pl1cn.e
    pl1cn.p
    @73
    eqid
    pl1cn.k
    evl1rhm
    cB
    @74
    cP
    @73
    cE
    pl1cn.b
    @74
    eqid
    rhmf
    cB
    @74
    cE
    ffn
    @75
    @72
    cB
    cE
    dffn3
    biimpi
    4syl
    syl
    pl1cn.3
    ffvelrnd
    cE
    @17
    pl1cn.e
    rneqi
    syl6eleq
    pf1ind
end
