include "crp.mm"
include "cr.mm"
include "wf.mm"
include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "ceu.mm"
include "cle.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clog.mm"
include "cdiv.mm"
include "wi.mm"
include "wtru.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "c1.mm"
include "cn.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ere.mm"
include "a1i.mm"
include "caddc.mm"
include "0re.mm"
include "epos.mm"
include "ltleii.mm"
include "wb.mm"
include "1re.mm"
include "addge02.mm"
include "mp2an.mm"
include "sylib.mm"
include "wa.mm"
include "relogcl.mm"
include "adantl.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "nnrp.mm"
include "sylan2.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmul.mm"
include "cc.mm"
include "cvv.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "cnelprrecn.mm"
include "recnd.mm"
include "ovexd.mm"
include "sqcl.mm"
include "halfcld.mm"
include "simpr.mm"
include "cres.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "relogf1o.mm"
include "f1of.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "wceq.mm"
include "2nn.mm"
include "dvexp.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "exp1.mm"
include "syl5eq.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "2cn.mm"
include "wne.mm"
include "2ne0.mm"
include "dvmptdivc.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "id.mm"
include "dvmptco.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "simp3r.mm"
include "simp2l.mm"
include "rpred.mm"
include "simp3l.mm"
include "simp2r.mm"
include "letrd.mm"
include "logdivle.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "ccxp.mm"
include "cxp1d.mm"
include "1rp.mm"
include "cxploglim.mm"
include "syl5eqbrr.mm"
include "dvfsumrlim3.mm"
include "trud.mm"

theorem logdivsum
  let vy: setvar y
  let cA: class A
  let vi: setvar i
  let cF: class F
  let cL: class L
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let wph: wff ph
  let cR: class R
  assume logdivsum.1: |- F = ( y e. RR+ |-> ( sum_ i e. ( 1 ... ( |_ ` y ) ) ( ( log ` i ) / i ) - ( ( ( log ` y ) ^ 2 ) / 2 ) ) )

  disjoint i y
  disjoint A i
  disjoint A y
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint L n
  disjoint L x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint R n
  disjoint R x
  assert |- ( F : RR+ --> RR /\ F e. dom ~~>r /\ ( ( F ~~>r L /\ A e. RR+ /\ _e <_ A ) -> ( abs ` ( ( F ` A ) - L ) ) <_ ( ( log ` A ) / A ) ) )

  proof
    crp
    cr
    cF
    wf
    cF
    crli
    cdm
    wcel
    cF
    cL
    crli
    wbr
    cA
    crp
    wcel
    ceu
    cA
    cle
    wbr
    w3a
    cA
    cF
    cfv
    cL
    cmin
    co
    cabs
    cfv
    cA
    clog
    cfv
    #
    cA
    cdiv
    co
    #
    cle
    wbr
    wi
    w3a
    wtru
    vy
    vy
    cv
    #
    clog
    cfv
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    @3
    @2
    cdiv
    co
    #
    vi
    cv
    #
    clog
    cfv
    #
    @7
    cdiv
    co
    #
    ceu
    crp
    cc0
    vi
    @1
    cF
    cL
    c1
    cr
    cA
    cn
    cc0
    cpnf
    cioo
    co
    crp
    ioorp
    eqcomi
    nnuz
    wtru
    1zzd
    ceu
    cr
    wcel
    #
    wtru
    ere
    a1i
    wtru
    cc0
    ceu
    cle
    wbr
    #
    c1
    ceu
    c1
    caddc
    co
    cle
    wbr
    #
    @11
    wtru
    cc0
    ceu
    0re
    ere
    epos
    ltleii
    a1i
    c1
    cr
    wcel
    @10
    @11
    @12
    wb
    1re
    ere
    c1
    ceu
    addge02
    mp2an
    sylib
    cc0
    cr
    wcel
    wtru
    0re
    a1i
    wtru
    @2
    crp
    wcel
    #
    wa
    #
    @4
    @14
    @3
    @13
    @3
    cr
    wcel
    #
    wtru
    @2
    relogcl
    #
    adantl
    #
    resqcld
    rehalfcld
    @13
    @6
    cr
    wcel
    #
    wtru
    @15
    @13
    @18
    @16
    @3
    @2
    rerpdivcl
    mpancom
    adantl
    #
    @2
    cn
    wcel
    wtru
    @13
    @18
    @2
    nnrp
    @19
    sylan2
    wtru
    cr
    vy
    crp
    @5
    cmpt
    cdv
    co
    vy
    crp
    @3
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    vy
    crp
    @6
    cmpt
    #
    wtru
    vy
    vx
    @3
    @20
    vx
    cv
    #
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    @23
    cr
    cc
    @5
    @3
    cvv
    cc
    crp
    cc
    cr
    cr
    cc
    cpr
    #
    wcel
    wtru
    reelprrecn
    a1i
    cc
    @26
    wcel
    wtru
    cnelprrecn
    a1i
    #
    @14
    @3
    @17
    recnd
    #
    @14
    c1
    @2
    cdiv
    ovexd
    wtru
    @23
    cc
    wcel
    #
    wa
    #
    @24
    @29
    @24
    cc
    wcel
    wtru
    @23
    sqcl
    adantl
    #
    halfcld
    wtru
    @29
    simpr
    wtru
    vy
    crp
    @20
    cmpt
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    vy
    crp
    @3
    cmpt
    #
    cdv
    co
    vy
    dvrelog
    wtru
    @32
    @33
    cr
    cdv
    wtru
    @32
    vy
    crp
    @2
    @32
    cfv
    #
    cmpt
    @33
    wtru
    vy
    crp
    cr
    @32
    crp
    cr
    @32
    wf1o
    crp
    cr
    @32
    wf
    wtru
    relogf1o
    crp
    cr
    @32
    f1of
    mp1i
    feqmptd
    vy
    crp
    @34
    @3
    @2
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    wtru
    cc
    vx
    cc
    @25
    cmpt
    cdv
    co
    vx
    cc
    c2
    @23
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cmpt
    vx
    cc
    @23
    cmpt
    wtru
    vx
    @24
    @35
    c2
    cc
    cvv
    cc
    @27
    @31
    @30
    c2
    @23
    cmul
    ovexd
    wtru
    cc
    vx
    cc
    @24
    cmpt
    cdv
    co
    #
    vx
    cc
    c2
    @23
    c2
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    vx
    cc
    @35
    cmpt
    c2
    cn
    wcel
    @37
    @41
    wceq
    wtru
    2nn
    vx
    c2
    dvexp
    mp1i
    wtru
    vx
    cc
    @40
    @35
    @30
    @39
    @23
    c2
    cmul
    @30
    @39
    @23
    c1
    cexp
    co
    #
    @23
    @38
    c1
    @23
    cexp
    2m1e1
    oveq2i
    @29
    @42
    @23
    wceq
    wtru
    @23
    exp1
    adantl
    syl5eq
    oveq2d
    mpteq2dva
    eqtrd
    c2
    cc
    wcel
    #
    wtru
    2cn
    a1i
    c2
    cc0
    wne
    #
    wtru
    2ne0
    a1i
    dvmptdivc
    wtru
    vx
    cc
    @36
    @23
    @29
    @36
    @23
    wceq
    #
    wtru
    @29
    @43
    @44
    @45
    2cn
    2ne0
    @23
    c2
    divcan3
    mp3an23
    adantl
    mpteq2dva
    eqtrd
    @23
    @3
    wceq
    #
    @24
    @4
    c2
    cdiv
    @23
    @3
    c2
    cexp
    oveq1
    oveq1d
    @46
    id
    dvmptco
    wtru
    vy
    crp
    @6
    @21
    @14
    @3
    @2
    @28
    @13
    @2
    cc
    wcel
    wtru
    @2
    rpcn
    #
    adantl
    @13
    @2
    cc0
    wne
    wtru
    @2
    rpne0
    adantl
    divrecd
    mpteq2dva
    eqtr4d
    @2
    @7
    wceq
    #
    @3
    @8
    @2
    @7
    cdiv
    @2
    @7
    clog
    fveq2
    @48
    id
    oveq12d
    wtru
    @13
    @7
    crp
    wcel
    #
    wa
    #
    ceu
    @2
    cle
    wbr
    #
    @2
    @7
    cle
    wbr
    #
    wa
    #
    w3a
    #
    @52
    @9
    @6
    cle
    wbr
    #
    wtru
    @50
    @51
    @52
    simp3r
    #
    @54
    @2
    cr
    wcel
    @51
    @7
    cr
    wcel
    ceu
    @7
    cle
    wbr
    @52
    @55
    wb
    @54
    @2
    wtru
    @13
    @49
    @53
    simp2l
    rpred
    #
    wtru
    @50
    @51
    @52
    simp3l
    #
    @54
    @7
    wtru
    @13
    @49
    @53
    simp2r
    rpred
    #
    @54
    ceu
    @2
    @7
    @10
    @54
    ere
    a1i
    @57
    @59
    @58
    @56
    letrd
    @2
    @7
    logdivle
    syl22anc
    mpbid
    logdivsum.1
    wtru
    @22
    vy
    crp
    @3
    @2
    c1
    ccxp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    crli
    vy
    crp
    @61
    @6
    @13
    @60
    @2
    @3
    cdiv
    @13
    @2
    @47
    cxp1d
    oveq2d
    mpteq2ia
    c1
    crp
    wcel
    @62
    cc0
    crli
    wbr
    wtru
    1rp
    c1
    vy
    cxploglim
    mp1i
    syl5eqbrr
    @2
    cA
    wceq
    #
    @3
    @0
    @2
    cA
    cdiv
    @2
    cA
    clog
    fveq2
    @63
    id
    oveq12d
    dvfsumrlim3
    trud
end
