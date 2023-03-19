include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cn0.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "cgsu.mm"
include "cco1.mm"
include "cc0.mm"
include "cfz.mm"
include "wf.mm"
include "fconst6g.mm"
include "nn0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "elmap.mm"
include "sylibr.mm"
include "adantl.mm"
include "eqidd.mm"
include "cmps.mm"
include "eqid.mm"
include "psr1bas2.mm"
include "psr1mulr.mm"
include "psr1baslem.mm"
include "simp2.mm"
include "simp3.mm"
include "psrmulfval.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "fmptco.mm"
include "psr1ring.mm"
include "ringcl.mm"
include "syl3an1.mm"
include "coe1fval3.mm"
include "syl.mm"
include "wa.mm"
include "c0.mm"
include "cbs.mm"
include "cfn.mm"
include "c0g.mm"
include "ccmn.mm"
include "simpl1.mm"
include "ringcmn.mm"
include "fzfi.mm"
include "a1i.mm"
include "simpll1.mm"
include "simpll2.mm"
include "coe1f2.mm"
include "elfznn0.mm"
include "ffvelrnd.mm"
include "simpll3.mm"
include "fznn0sub.mm"
include "syl3anc.mm"
include "fmptd.mm"
include "cfsupp.mm"
include "cvv.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "mptex.mm"
include "funmpt.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "pm3.2i.mm"
include "suppssfifsupp.mm"
include "mp2an.mm"
include "wf1o.mm"
include "coe1mul2lem2.mm"
include "gsumf1o.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "wb.mm"
include "simplr.mm"
include "elrabi.mm"
include "coe1mul2lem1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fvcoe1.mm"
include "df1o2.mm"
include "0ex.mm"
include "mapsnconst.mm"
include "vex.mm"
include "fvexd.mm"
include "ofc12.mm"
include "eqtrd.mm"
include "coe1fv.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"
include "3eqtr4d.mm"

theorem coe1mul2
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume coe1mul2.s: |- S = ( PwSer1 ` R )
  assume coe1mul2.t: |- .xb = ( .r ` S )
  assume coe1mul2.u: |- .x. = ( .r ` R )
  assume coe1mul2.b: |- B = ( Base ` S )

  disjoint k x
  disjoint B k
  disjoint B x
  disjoint F k
  disjoint F x
  disjoint .x. k
  disjoint .x. x
  disjoint G k
  disjoint G x
  disjoint R k
  disjoint R x
  disjoint .xb k
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a k
  disjoint a x
  disjoint b c
  disjoint b d
  disjoint b k
  disjoint b x
  disjoint c d
  disjoint c k
  disjoint c x
  disjoint d k
  disjoint d x
  disjoint B b
  disjoint B c
  disjoint F b
  disjoint F c
  disjoint .x. b
  disjoint .x. c
  disjoint G b
  disjoint G c
  disjoint R b
  disjoint R c
  assert |- ( ( R e. Ring /\ F e. B /\ G e. B ) -> ( coe1 ` ( F .xb G ) ) = ( k e. NN0 |-> ( R gsum ( x e. ( 0 ... k ) |-> ( ( ( coe1 ` F ) ` x ) .x. ( ( coe1 ` G ) ` ( k - x ) ) ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cF
    cG
    c.xb
    co
    #
    vk
    cn0
    c1o
    vk
    cv
    #
    csn
    cxp
    #
    cmpt
    #
    ccom
    #
    vk
    cn0
    cR
    vc
    vd
    cv
    #
    @6
    cle
    cofr
    #
    wbr
    #
    vd
    cn0
    c1o
    cmap
    co
    #
    crab
    #
    vc
    cv
    #
    cF
    cfv
    #
    @6
    @14
    cmin
    cof
    #
    co
    #
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @4
    cco1
    cfv
    #
    vk
    cn0
    cR
    vx
    cc0
    @5
    cfz
    co
    #
    vx
    cv
    #
    cF
    cco1
    cfv
    #
    cfv
    #
    @5
    @24
    cmin
    co
    #
    cG
    cco1
    cfv
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @3
    vk
    vb
    cn0
    @12
    @6
    cR
    vc
    @9
    vb
    cv
    #
    @10
    wbr
    #
    vd
    @12
    crab
    #
    @15
    @33
    @14
    @16
    co
    #
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    @21
    @7
    @4
    @5
    cn0
    wcel
    #
    @6
    @12
    wcel
    #
    @3
    @40
    c1o
    cn0
    @6
    wf
    @41
    c1o
    @5
    cn0
    fconst6g
    cn0
    c1o
    @6
    nn0ex
    c1o
    con0
    1on
    elexi
    elmap
    sylibr
    adantl
    @3
    @7
    eqidd
    @3
    vc
    vd
    cB
    @12
    cR
    c1o
    cR
    cmps
    co
    #
    c.xb
    c.x
    va
    vb
    cF
    cG
    c1o
    @42
    eqid
    #
    cB
    cR
    cS
    @42
    coe1mul2.s
    coe1mul2.b
    @43
    psr1bas2
    coe1mul2.u
    cR
    @42
    c.xb
    cS
    coe1mul2.s
    @43
    coe1mul2.t
    psr1mulr
    va
    psr1baslem
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    psrmulfval
    @33
    @6
    wceq
    #
    @39
    @20
    cR
    cgsu
    @44
    vc
    @35
    @38
    @13
    @19
    @44
    @34
    @11
    vd
    @12
    @33
    @6
    @9
    @10
    breq2
    rabbidv
    @44
    @37
    @18
    @15
    c.x
    @44
    @36
    @17
    cG
    @33
    @6
    @14
    @16
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    fmptco
    @3
    @4
    cB
    wcel
    #
    @22
    @8
    wceq
    @0
    cS
    crg
    wcel
    @1
    @2
    @45
    cR
    cS
    coe1mul2.s
    psr1ring
    cB
    cS
    c.xb
    cF
    cG
    coe1mul2.b
    coe1mul2.t
    ringcl
    syl3an1
    vk
    @22
    cB
    cS
    cR
    @4
    @7
    @22
    eqid
    coe1mul2.b
    coe1mul2.s
    @7
    eqid
    coe1fval3
    syl
    @3
    vk
    cn0
    @32
    @21
    @3
    @40
    wa
    #
    @32
    cR
    @31
    vc
    @13
    c0
    @14
    cfv
    #
    cmpt
    #
    ccom
    #
    cgsu
    co
    @21
    @46
    @23
    cR
    cbs
    cfv
    #
    @13
    @31
    cR
    @48
    cfn
    cR
    c0g
    cfv
    #
    @50
    eqid
    #
    @51
    eqid
    @46
    @0
    cR
    ccmn
    wcel
    @0
    @1
    @2
    @40
    simpl1
    cR
    ringcmn
    syl
    @23
    cfn
    wcel
    #
    @46
    cc0
    @5
    fzfi
    #
    a1i
    @46
    vx
    @23
    @30
    @50
    @31
    @46
    @24
    @23
    wcel
    #
    wa
    #
    @0
    @26
    @50
    wcel
    @29
    @50
    wcel
    @30
    @50
    wcel
    @0
    @1
    @2
    @40
    @55
    simpll1
    @56
    cn0
    @50
    @24
    @25
    @56
    @1
    cn0
    @50
    @25
    wf
    @0
    @1
    @2
    @40
    @55
    simpll2
    @25
    cB
    cS
    cR
    cF
    @50
    @25
    eqid
    #
    coe1mul2.b
    coe1mul2.s
    @52
    coe1f2
    syl
    @55
    @24
    cn0
    wcel
    @46
    @24
    @5
    elfznn0
    adantl
    ffvelrnd
    @56
    cn0
    @50
    @27
    @28
    @56
    @2
    cn0
    @50
    @28
    wf
    @0
    @1
    @2
    @40
    @55
    simpll3
    @28
    cB
    cS
    cR
    cG
    @50
    @28
    eqid
    #
    coe1mul2.b
    coe1mul2.s
    @52
    coe1f2
    syl
    @55
    @27
    cn0
    wcel
    @46
    @24
    cc0
    @5
    fznn0sub
    adantl
    ffvelrnd
    @50
    cR
    c.x
    @26
    @29
    @52
    coe1mul2.u
    ringcl
    syl3anc
    @31
    eqid
    #
    fmptd
    @31
    @51
    cfsupp
    wbr
    #
    @46
    @31
    cvv
    wcel
    #
    @31
    wfun
    #
    @51
    cvv
    wcel
    #
    w3a
    @53
    @31
    @51
    csupp
    co
    #
    @23
    wss
    #
    wa
    @60
    @61
    @62
    @63
    vx
    @23
    @30
    @23
    cfn
    @54
    elexi
    mptex
    vx
    @23
    @30
    funmpt
    cR
    c0g
    fvex
    3pm3.2i
    @53
    @65
    @54
    @64
    @31
    cdm
    @23
    @31
    @51
    suppssdm
    vx
    @23
    @30
    @31
    @59
    dmmptss
    sstri
    pm3.2i
    @23
    @31
    cvv
    cvv
    @51
    suppssfifsupp
    mp2an
    a1i
    @40
    @13
    @23
    @48
    wf1o
    @3
    vk
    @13
    vc
    vd
    @13
    eqid
    coe1mul2lem2
    adantl
    gsumf1o
    @46
    @49
    @20
    cR
    cgsu
    @46
    @49
    vc
    @13
    @47
    @25
    cfv
    #
    @5
    @47
    cmin
    co
    #
    @28
    cfv
    #
    c.x
    co
    #
    cmpt
    @20
    @46
    vc
    vx
    @13
    @23
    @47
    @30
    @69
    @48
    @31
    @46
    @14
    @13
    wcel
    #
    wa
    #
    @14
    @6
    @10
    wbr
    #
    @47
    @23
    wcel
    #
    @70
    @72
    @46
    @70
    @14
    @12
    wcel
    #
    @72
    @11
    @72
    vd
    @14
    @12
    @9
    @14
    @6
    @10
    breq1
    elrab
    simprbi
    adantl
    @71
    @40
    @74
    @72
    @73
    wb
    @3
    @40
    @70
    simplr
    @70
    @74
    @46
    @11
    vd
    @14
    @12
    elrabi
    adantl
    #
    @5
    @14
    coe1mul2lem1
    syl2anc
    mpbid
    #
    @46
    @48
    eqidd
    @46
    @31
    eqidd
    @24
    @47
    wceq
    #
    @26
    @66
    @29
    @68
    c.x
    @24
    @47
    @25
    fveq2
    @77
    @27
    @67
    @28
    @24
    @47
    @5
    cmin
    oveq2
    fveq2d
    oveq12d
    fmptco
    @46
    vc
    @13
    @19
    @69
    @71
    @15
    @66
    @18
    @68
    c.x
    @71
    @1
    @74
    @15
    @66
    wceq
    @0
    @1
    @2
    @40
    @70
    simpll2
    @75
    @25
    cF
    cB
    @14
    @57
    fvcoe1
    syl2anc
    @71
    @18
    c1o
    @67
    csn
    cxp
    #
    cG
    cfv
    #
    @68
    @71
    @17
    @78
    cG
    @71
    @17
    @6
    c1o
    @47
    csn
    cxp
    #
    @16
    co
    @78
    @71
    @14
    @80
    @6
    @16
    @71
    @74
    @14
    @80
    wceq
    @75
    cn0
    c1o
    @14
    c0
    df1o2
    nn0ex
    0ex
    mapsnconst
    syl
    oveq2d
    @71
    c1o
    @5
    @47
    cmin
    con0
    cvv
    cvv
    c1o
    con0
    wcel
    @71
    1on
    a1i
    @5
    cvv
    wcel
    @71
    vk
    vex
    a1i
    @71
    c0
    @14
    fvexd
    ofc12
    eqtrd
    fveq2d
    @71
    @2
    @67
    cn0
    wcel
    #
    @68
    @79
    wceq
    @0
    @1
    @2
    @40
    @70
    simpll3
    @71
    @73
    @81
    @76
    @47
    cc0
    @5
    fznn0sub
    syl
    @28
    cG
    @67
    cB
    @58
    coe1fv
    syl2anc
    eqtr4d
    oveq12d
    mpteq2dva
    eqtr4d
    oveq2d
    eqtrd
    mpteq2dva
    3eqtr4d
end
