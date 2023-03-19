include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wa.mm"
include "ccom.mm"
include "cbs.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "simpll1.mm"
include "wf.mm"
include "simp3.mm"
include "psrelbas.mm"
include "elrabi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simp2.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "strov2rcl.mm"
include "3ad2ant3.mm"
include "simplr.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "ringcl.mm"
include "fmptd.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "cfsupp.mm"
include "mptexg.mm"
include "mp1i.mm"
include "funmpt.mm"
include "fvex.mm"
include "psrbaglefi.mm"
include "sylan.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmmptss.mm"
include "sstri.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "wf1o.mm"
include "psrbagconf1o.mm"
include "gsumf1o.mm"
include "eqidd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "psrbagf.mm"
include "cc.mm"
include "nn0cn.mm"
include "nncan.mm"
include "adantl.mm"
include "caonncan.mm"
include "oveq2d.mm"
include "opprmul.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "mptex.mm"
include "id.mm"
include "coppr.mm"
include "eqeltri.mm"
include "opprbas.mm"
include "cplusg.mm"
include "oppradd.mm"
include "gsumpropd.mm"
include "3eqtrd.mm"
include "psrmulfval.mm"
include "psrbaspropd.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "eleqtrd.mm"
include "3eqtr4rd.mm"

theorem psropprmul
  let cB: class B
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let va: setvar a
  let vd: setvar d
  assume psropprmul.y: |- Y = ( I mPwSer R )
  assume psropprmul.s: |- S = ( oppR ` R )
  assume psropprmul.z: |- Z = ( I mPwSer S )
  assume psropprmul.t: |- .x. = ( .r ` Y )
  assume psropprmul.u: |- .xb = ( .r ` Z )
  assume psropprmul.b: |- B = ( Base ` Y )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. B ) -> ( F .xb G ) = ( G .x. F ) )

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
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    va
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cR
    ve
    vd
    cv
    vb
    cv
    #
    cle
    cofr
    wbr
    #
    vd
    @6
    crab
    #
    ve
    cv
    #
    cG
    cfv
    #
    @7
    @10
    cmin
    cof
    #
    co
    #
    cF
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    vb
    @6
    cS
    vc
    @9
    vc
    cv
    #
    cF
    cfv
    #
    @7
    @19
    @12
    co
    #
    cG
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    cG
    cF
    c.x
    co
    cF
    cG
    c.xb
    co
    @3
    vb
    @6
    @18
    @26
    @3
    @7
    @6
    wcel
    #
    wa
    #
    @18
    cR
    @17
    vc
    @9
    @21
    cmpt
    #
    ccom
    #
    cgsu
    co
    cR
    @25
    cgsu
    co
    #
    @26
    @28
    @9
    cR
    cbs
    cfv
    #
    @9
    @17
    cR
    @29
    cvv
    cR
    c0g
    cfv
    #
    @32
    eqid
    #
    @33
    eqid
    @3
    cR
    ccmn
    wcel
    #
    @27
    @0
    @1
    @35
    @2
    cR
    ringcmn
    3ad2ant1
    adantr
    @9
    cvv
    wcel
    #
    @28
    @8
    vd
    @6
    @4
    va
    @5
    cn0
    cI
    cmap
    ovex
    rabex
    rabex
    #
    a1i
    @28
    ve
    @9
    @16
    @32
    @17
    @28
    @10
    @9
    wcel
    #
    wa
    #
    @0
    @11
    @32
    wcel
    #
    @14
    @32
    wcel
    @16
    @32
    wcel
    @0
    @1
    @2
    @27
    @38
    simpll1
    @28
    @6
    @32
    cG
    wf
    #
    @10
    @6
    wcel
    @40
    @38
    @3
    @41
    @27
    @3
    cB
    @6
    cR
    cY
    va
    cI
    @32
    cG
    psropprmul.y
    @34
    @6
    eqid
    #
    psropprmul.b
    @0
    @1
    @2
    simp3
    #
    psrelbas
    adantr
    @8
    vd
    @10
    @6
    elrabi
    @6
    @32
    @10
    cG
    ffvelrn
    syl2an
    @39
    @6
    @32
    @13
    cF
    @3
    @6
    @32
    cF
    wf
    @27
    @38
    @3
    cB
    @6
    cR
    cY
    va
    cI
    @32
    cF
    psropprmul.y
    @34
    @42
    psropprmul.b
    @0
    @1
    @2
    simp2
    #
    psrelbas
    ad2antrr
    @39
    @9
    @6
    @13
    @8
    vd
    @6
    ssrab2
    @39
    cI
    cvv
    wcel
    #
    @27
    @38
    @13
    @9
    wcel
    @3
    @45
    @27
    @38
    @2
    @0
    @45
    @1
    cB
    cR
    cY
    cmps
    cI
    cG
    psropprmul.y
    psropprmul.b
    reldmpsr
    strov2rcl
    3ad2ant3
    #
    ad2antrr
    @3
    @27
    @38
    simplr
    @28
    @38
    simpr
    vd
    @6
    @9
    va
    @7
    cI
    cvv
    @10
    @42
    @9
    eqid
    #
    psrbagconcl
    syl3anc
    sseldi
    ffvelrnd
    @32
    cR
    @15
    @11
    @14
    @34
    @15
    eqid
    #
    ringcl
    syl3anc
    @17
    eqid
    #
    fmptd
    @28
    @17
    cvv
    wcel
    #
    @17
    wfun
    #
    @33
    cvv
    wcel
    #
    @9
    cfn
    wcel
    #
    @17
    @33
    csupp
    co
    #
    @9
    wss
    #
    @17
    @33
    cfsupp
    wbr
    @36
    @50
    @28
    @37
    ve
    @9
    @16
    cvv
    mptexg
    mp1i
    @51
    @28
    ve
    @9
    @16
    funmpt
    a1i
    @52
    @28
    cR
    c0g
    fvex
    a1i
    @3
    @45
    @27
    @53
    @46
    vd
    @6
    va
    @7
    cI
    cvv
    @42
    psrbaglefi
    sylan
    @55
    @28
    @54
    @17
    cdm
    @9
    @17
    @33
    suppssdm
    ve
    @9
    @16
    @17
    @49
    dmmptss
    sstri
    a1i
    @9
    @17
    cvv
    cvv
    @33
    suppssfifsupp
    syl32anc
    @3
    @45
    @27
    @9
    @9
    @29
    wf1o
    @46
    vc
    vd
    @6
    @9
    va
    @7
    cI
    cvv
    @42
    @47
    psrbagconf1o
    sylan
    gsumf1o
    @28
    @30
    @25
    cR
    cgsu
    @28
    @30
    vc
    @9
    @22
    @7
    @21
    @12
    co
    #
    cF
    cfv
    #
    @15
    co
    #
    cmpt
    @25
    @28
    vc
    ve
    @9
    @9
    @21
    @16
    @58
    @29
    @17
    @28
    @19
    @9
    wcel
    #
    wa
    #
    @45
    @27
    @59
    @21
    @9
    wcel
    @3
    @45
    @27
    @59
    @46
    ad2antrr
    #
    @3
    @27
    @59
    simplr
    @28
    @59
    simpr
    vd
    @6
    @9
    va
    @7
    cI
    cvv
    @19
    @42
    @47
    psrbagconcl
    syl3anc
    @28
    @29
    eqidd
    @28
    @17
    eqidd
    @10
    @21
    wceq
    #
    @11
    @22
    @14
    @57
    @15
    @10
    @21
    cG
    fveq2
    @62
    @13
    @56
    cF
    @10
    @21
    @7
    @12
    oveq2
    fveq2d
    oveq12d
    fmptco
    @28
    vc
    @9
    @58
    @24
    @60
    @58
    @22
    @20
    @15
    co
    @24
    @60
    @57
    @20
    @22
    @15
    @60
    @56
    @19
    cF
    @60
    ve
    vf
    @7
    @19
    cn0
    cI
    cmin
    cvv
    @61
    @28
    cI
    cn0
    @7
    wf
    #
    @59
    @3
    @45
    @27
    @63
    @46
    @6
    va
    @7
    cI
    cvv
    @42
    psrbagf
    sylan
    adantr
    @28
    @45
    @19
    @6
    wcel
    cI
    cn0
    @19
    wf
    @59
    @3
    @45
    @27
    @46
    adantr
    @8
    vd
    @19
    @6
    elrabi
    @6
    va
    @19
    cI
    cvv
    @42
    psrbagf
    syl2an
    @10
    cn0
    wcel
    #
    vf
    cv
    #
    cn0
    wcel
    #
    wa
    @10
    @10
    @65
    cmin
    co
    cmin
    co
    @65
    wceq
    #
    @60
    @64
    @10
    cc
    wcel
    @65
    cc
    wcel
    @67
    @66
    @10
    nn0cn
    @65
    nn0cn
    @10
    @65
    nncan
    syl2an
    adantl
    caonncan
    fveq2d
    oveq2d
    @32
    cR
    @23
    @15
    cS
    @20
    @22
    @34
    @48
    psropprmul.s
    @23
    eqid
    #
    opprmul
    syl6eqr
    mpteq2dva
    eqtrd
    oveq2d
    @3
    @31
    @26
    wceq
    #
    @27
    @0
    @1
    @69
    @2
    @0
    @25
    cR
    cS
    cvv
    crg
    cvv
    @25
    cvv
    wcel
    @0
    vc
    @9
    @24
    @37
    mptex
    a1i
    @0
    id
    cS
    cvv
    wcel
    @0
    cS
    cR
    coppr
    cfv
    cvv
    psropprmul.s
    cR
    coppr
    fvex
    eqeltri
    a1i
    @32
    cS
    cbs
    cfv
    wceq
    #
    @0
    @32
    cR
    cS
    psropprmul.s
    @34
    opprbas
    #
    a1i
    cR
    cplusg
    cfv
    #
    cS
    cplusg
    cfv
    wceq
    @0
    @72
    cR
    cS
    psropprmul.s
    @72
    eqid
    oppradd
    a1i
    gsumpropd
    3ad2ant1
    adantr
    3eqtrd
    mpteq2dva
    @3
    ve
    vd
    cB
    @6
    cR
    cY
    c.x
    @15
    va
    vb
    cG
    cF
    cI
    psropprmul.y
    psropprmul.b
    @48
    psropprmul.t
    @42
    @43
    @44
    psrmulfval
    @3
    vc
    vd
    cZ
    cbs
    cfv
    #
    @6
    cS
    cZ
    c.xb
    @23
    va
    vb
    cF
    cG
    cI
    psropprmul.z
    @73
    eqid
    @68
    psropprmul.u
    @42
    @3
    cF
    cB
    @73
    @44
    @3
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cI
    cS
    cmps
    co
    #
    cbs
    cfv
    cB
    @73
    @3
    cR
    cS
    cI
    @70
    @3
    @71
    a1i
    psrbaspropd
    cB
    cY
    cbs
    cfv
    @75
    psropprmul.b
    cY
    @74
    cbs
    psropprmul.y
    fveq2i
    eqtri
    cZ
    @76
    cbs
    psropprmul.z
    fveq2i
    3eqtr4g
    #
    eleqtrd
    @3
    cG
    cB
    @73
    @43
    @77
    eleqtrd
    psrmulfval
    3eqtr4rd
end
