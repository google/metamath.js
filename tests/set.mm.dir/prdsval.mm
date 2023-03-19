include "cprds.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "chom.mm"
include "cco.mm"
include "cpr.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cixp.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "ctopn.mm"
include "ccom.mm"
include "cpt.mm"
include "wss.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "csb.mm"
include "wceq.mm"
include "df-prds.mm"
include "a1i.mm"
include "ciun.mm"
include "cmap.mm"
include "wcel.mm"
include "cuni.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "baseid.mm"
include "strfvss.mm"
include "fvssunirn.mm"
include "rnss.mm"
include "uniss.mm"
include "mp2b.mm"
include "sstri.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "ssexi.mm"
include "ixpssmap2g.mm"
include "ax-mp.mm"
include "ovex.mm"
include "ssex.mm"
include "mp1i.mm"
include "simpr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "ixpeq2dv.mm"
include "dmeqd.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "ixpeq1d.mm"
include "3eqtr4d.mm"
include "cpw.mm"
include "wf.mm"
include "ovssunirn.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "df-hom.mm"
include "ss2ixp.mm"
include "dmex.mm"
include "ixpconst.mm"
include "sseqtri.mm"
include "elpw2.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "xpex.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "adantr.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "ad3antrrr.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "opeq2d.mm"
include "mpteq12dv.mm"
include "ad4antr.mm"
include "tpeq123d.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "uneq12d.mm"
include "coeq2d.mm"
include "sseq2d.mm"
include "wb.mm"
include "breqd.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "supeq1d.mm"
include "sqxpeqd.mm"
include "preq12d.mm"
include "csbied2.mm"
include "anasss.mm"
include "elex.mm"
include "syl.mm"
include "tpex.mm"
include "unex.mm"
include "prex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem prdsval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let c.xi: class .,
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  assume prdsval.p: |- P = ( S Xs_ R )
  assume prdsval.k: |- K = ( Base ` S )
  assume prdsval.i: |- ( ph -> dom R = I )
  assume prdsval.b: |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) )
  assume prdsval.a: |- ( ph -> .+ = ( f e. B , g e. B |-> ( x e. I |-> ( ( f ` x ) ( +g ` ( R ` x ) ) ( g ` x ) ) ) ) )
  assume prdsval.t: |- ( ph -> .X. = ( f e. B , g e. B |-> ( x e. I |-> ( ( f ` x ) ( .r ` ( R ` x ) ) ( g ` x ) ) ) ) )
  assume prdsval.m: |- ( ph -> .x. = ( f e. K , g e. B |-> ( x e. I |-> ( f ( .s ` ( R ` x ) ) ( g ` x ) ) ) ) )
  assume prdsval.j: |- ( ph -> ., = ( f e. B , g e. B |-> ( S gsum ( x e. I |-> ( ( f ` x ) ( .i ` ( R ` x ) ) ( g ` x ) ) ) ) ) )
  assume prdsval.o: |- ( ph -> O = ( Xt_ ` ( TopOpen o. R ) ) )
  assume prdsval.l: |- ( ph -> .<_ = { <. f , g >. | ( { f , g } C_ B /\ A. x e. I ( f ` x ) ( le ` ( R ` x ) ) ( g ` x ) ) } )
  assume prdsval.d: |- ( ph -> D = ( f e. B , g e. B |-> sup ( ( ran ( x e. I |-> ( ( f ` x ) ( dist ` ( R ` x ) ) ( g ` x ) ) ) u. { 0 } ) , RR* , < ) ) )
  assume prdsval.h: |- ( ph -> H = ( f e. B , g e. B |-> X_ x e. I ( ( f ` x ) ( Hom ` ( R ` x ) ) ( g ` x ) ) ) )
  assume prdsval.x: |- ( ph -> .xb = ( a e. ( B X. B ) , c e. B |-> ( d e. ( c H ( 2nd ` a ) ) , e e. ( H ` a ) |-> ( x e. I |-> ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >. ( comp ` ( R ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) )
  assume prdsval.s: |- ( ph -> S e. W )
  assume prdsval.r: |- ( ph -> R e. Z )

  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint B a
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint B c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint B d
  disjoint e f
  disjoint e g
  disjoint B e
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint H a
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint a x
  disjoint a ph
  disjoint c x
  disjoint c ph
  disjoint d x
  disjoint d ph
  disjoint e x
  disjoint e ph
  disjoint f x
  disjoint f ph
  disjoint g x
  disjoint g ph
  disjoint ph x
  disjoint I x
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint S a
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint h r
  disjoint h s
  disjoint h v
  disjoint .+ h
  disjoint r s
  disjoint r v
  disjoint .+ r
  disjoint s v
  disjoint .+ s
  disjoint .+ v
  disjoint .<_ h
  disjoint .<_ r
  disjoint .<_ s
  disjoint .<_ v
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a v
  disjoint c h
  disjoint c r
  disjoint c s
  disjoint c v
  disjoint d h
  disjoint d r
  disjoint d s
  disjoint d v
  disjoint e h
  disjoint e r
  disjoint e s
  disjoint e v
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f v
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g v
  disjoint B h
  disjoint B r
  disjoint B s
  disjoint B v
  disjoint H h
  disjoint H r
  disjoint H s
  disjoint H v
  disjoint h x
  disjoint h ph
  disjoint r x
  disjoint ph r
  disjoint s x
  disjoint ph s
  disjoint v x
  disjoint ph v
  disjoint D h
  disjoint D r
  disjoint D s
  disjoint D v
  disjoint O h
  disjoint O r
  disjoint O s
  disjoint O v
  disjoint .X. h
  disjoint .X. r
  disjoint .X. s
  disjoint .X. v
  disjoint .xb h
  disjoint .xb r
  disjoint .xb s
  disjoint .xb v
  disjoint R h
  disjoint R r
  disjoint R s
  disjoint R v
  disjoint S h
  disjoint S r
  disjoint S s
  disjoint S v
  disjoint .x. h
  disjoint .x. r
  disjoint .x. s
  disjoint .x. v
  disjoint ., h
  disjoint ., r
  disjoint ., s
  disjoint ., v
  assert |- ( ph -> P = ( ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , S >. , <. ( .s ` ndx ) , .x. >. , <. ( .i ` ndx ) , ., >. } ) u. ( { <. ( TopSet ` ndx ) , O >. , <. ( le ` ndx ) , .<_ >. , <. ( dist ` ndx ) , D >. } u. { <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .xb >. } ) ) )

  proof
    wph
    cP
    cS
    cR
    cprds
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cnx
    cmulr
    cfv
    #
    c.xp
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    #
    cS
    cop
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    #
    cnx
    cip
    cfv
    #
    c.xi
    cop
    #
    ctp
    #
    cun
    #
    cnx
    cts
    cfv
    #
    cO
    cop
    #
    cnx
    cple
    cfv
    #
    c.le
    cop
    #
    cnx
    cds
    cfv
    #
    cD
    cop
    #
    ctp
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    #
    cnx
    cco
    cfv
    #
    c.xb
    cop
    #
    cpr
    #
    cun
    #
    cun
    #
    prdsval.p
    wph
    vs
    vr
    cS
    cR
    cvv
    cvv
    vv
    vx
    vr
    cv
    #
    cdm
    #
    vx
    cv
    #
    @29
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    vh
    vf
    vg
    vv
    cv
    #
    @35
    vx
    @30
    @31
    vf
    cv
    #
    cfv
    #
    @31
    vg
    cv
    #
    cfv
    #
    @32
    chom
    cfv
    #
    co
    #
    cixp
    #
    cmpt2
    #
    @0
    @35
    cop
    #
    @2
    vf
    vg
    @35
    @35
    vx
    @30
    @37
    @39
    @32
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    @4
    vf
    vg
    @35
    @35
    vx
    @30
    @37
    @39
    @32
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    @7
    vs
    cv
    #
    cop
    #
    @9
    vf
    vg
    @56
    cbs
    cfv
    #
    @35
    vx
    @30
    @36
    @39
    @32
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    @11
    vf
    vg
    @35
    @35
    @56
    vx
    @30
    @37
    @39
    @32
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    cun
    #
    @15
    ctopn
    @29
    ccom
    #
    cpt
    cfv
    #
    cop
    #
    @17
    @36
    @38
    cpr
    #
    @35
    wss
    #
    @37
    @39
    @32
    cple
    cfv
    #
    wbr
    #
    vx
    @30
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    cop
    #
    @19
    vf
    vg
    @35
    @35
    vx
    @30
    @37
    @39
    @32
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    @22
    vh
    cv
    #
    cop
    #
    @24
    va
    vc
    @35
    @35
    cxp
    #
    @35
    vd
    ve
    vc
    cv
    #
    va
    cv
    #
    c2nd
    cfv
    #
    @93
    co
    #
    @97
    @93
    cfv
    #
    vx
    @30
    @31
    vd
    cv
    cfv
    #
    @31
    ve
    cv
    cfv
    #
    @31
    @97
    c1st
    cfv
    cfv
    @31
    @98
    cfv
    cop
    #
    @31
    @96
    cfv
    #
    @32
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cun
    #
    cun
    #
    csb
    #
    csb
    #
    @28
    cprds
    cvv
    cprds
    vs
    vr
    cvv
    cvv
    @116
    cmpt2
    wceq
    wph
    vx
    vv
    ve
    vf
    vg
    vh
    vs
    vr
    va
    vc
    vd
    df-prds
    a1i
    wph
    @56
    cS
    wceq
    #
    @29
    cR
    wceq
    #
    @116
    @28
    wceq
    wph
    @117
    wa
    #
    @118
    wa
    #
    vv
    @34
    cB
    @115
    @28
    cvv
    @34
    vx
    @30
    @33
    ciun
    #
    @30
    cmap
    co
    #
    wss
    #
    @34
    cvv
    wcel
    @120
    @121
    cvv
    wcel
    @123
    @121
    @29
    crn
    #
    cuni
    #
    crn
    #
    cuni
    #
    @126
    @125
    @124
    @29
    vr
    vex
    #
    rnex
    uniex
    rnex
    uniex
    #
    @121
    @127
    wss
    @33
    @127
    wss
    #
    vx
    @30
    wral
    @130
    vx
    @30
    @33
    @32
    crn
    #
    cuni
    #
    @127
    @32
    cbs
    @0
    baseid
    strfvss
    @32
    @125
    wss
    @131
    @126
    wss
    @132
    @127
    wss
    @29
    @31
    fvssunirn
    @32
    @125
    rnss
    @131
    @126
    uniss
    mp2b
    #
    sstri
    rgenw
    vx
    @30
    @33
    @127
    iunss
    mpbir
    ssexi
    vx
    @30
    @33
    cvv
    ixpssmap2g
    ax-mp
    @34
    @122
    @121
    @30
    cmap
    ovex
    ssex
    mp1i
    @120
    vx
    cI
    @33
    cixp
    vx
    cI
    @31
    cR
    cfv
    #
    cbs
    cfv
    #
    cixp
    #
    @34
    cB
    @120
    vx
    cI
    @33
    @135
    @120
    @32
    @134
    cbs
    @120
    @31
    @29
    cR
    @119
    @118
    simpr
    #
    fveq1d
    #
    fveq2d
    ixpeq2dv
    @120
    vx
    @30
    cI
    @33
    @120
    @30
    cR
    cdm
    #
    cI
    @120
    @29
    cR
    @137
    dmeqd
    wph
    @139
    cI
    wceq
    @117
    @118
    prdsval.i
    ad2antrr
    eqtrd
    #
    ixpeq1d
    wph
    cB
    @136
    wceq
    @117
    @118
    prdsval.b
    ad2antrr
    3eqtr4d
    @120
    @35
    cB
    wceq
    #
    wa
    #
    vh
    @43
    cH
    @114
    @28
    cvv
    @43
    cvv
    wcel
    #
    @142
    @95
    @127
    crn
    #
    cuni
    #
    @30
    cmap
    co
    #
    cpw
    #
    @43
    wf
    #
    @95
    cvv
    wcel
    @147
    cvv
    wcel
    @143
    @42
    @147
    wcel
    #
    vg
    @35
    wral
    vf
    @35
    wral
    @148
    @149
    vf
    vg
    @35
    @35
    @149
    @42
    @146
    wss
    @42
    vx
    @30
    @145
    cixp
    #
    @146
    @41
    @145
    wss
    #
    vx
    @30
    wral
    @42
    @150
    wss
    @151
    vx
    @30
    @41
    @40
    crn
    #
    cuni
    #
    @145
    @40
    @37
    @39
    ovssunirn
    @40
    @127
    wss
    @152
    @144
    wss
    @153
    @145
    wss
    @40
    @132
    @127
    @32
    chom
    c1
    c4
    cdc
    df-hom
    strfvss
    @133
    sstri
    @40
    @127
    rnss
    @152
    @144
    uniss
    mp2b
    sstri
    rgenw
    vx
    @30
    @41
    @145
    ss2ixp
    ax-mp
    vx
    @30
    @145
    @29
    @128
    dmex
    @144
    @127
    @129
    rnex
    uniex
    ixpconst
    sseqtri
    @42
    @146
    @145
    @30
    cmap
    ovex
    #
    elpw2
    mpbir
    rgen2w
    vf
    vg
    @35
    @35
    @42
    @147
    @43
    @43
    eqid
    fmpt2
    mpbi
    @35
    @35
    vv
    vex
    #
    @155
    xpex
    @146
    @154
    pwex
    @95
    @147
    @43
    cvv
    cvv
    fex2
    mp3an
    a1i
    @142
    @43
    vf
    vg
    cB
    cB
    vx
    cI
    @37
    @39
    @134
    chom
    cfv
    #
    co
    #
    cixp
    #
    cmpt2
    #
    cH
    @142
    vf
    vg
    @35
    @35
    @42
    cB
    cB
    @158
    @120
    @141
    simpr
    #
    @160
    @142
    @42
    vx
    cI
    @41
    cixp
    #
    @158
    @142
    vx
    @30
    cI
    @41
    @120
    @30
    cI
    wceq
    @141
    @140
    adantr
    ixpeq1d
    @120
    @161
    @158
    wceq
    @141
    @120
    vx
    cI
    @41
    @157
    @120
    @40
    @156
    @37
    @39
    @120
    @32
    @134
    chom
    @138
    fveq2d
    oveqd
    ixpeq2dv
    adantr
    eqtrd
    mpt2eq123dv
    wph
    cH
    @159
    wceq
    @117
    @118
    @141
    prdsval.h
    ad3antrrr
    eqtr4d
    @142
    @93
    cH
    wceq
    #
    wa
    #
    @71
    @14
    @113
    @27
    @163
    @55
    @6
    @70
    @13
    @163
    @44
    @1
    @49
    @3
    @54
    @5
    @163
    @35
    cB
    @0
    @120
    @141
    @162
    simplr
    #
    opeq2d
    @163
    @48
    c.pl
    @2
    @163
    @48
    vf
    vg
    cB
    cB
    vx
    cI
    @37
    @39
    @134
    cplusg
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    c.pl
    @142
    @48
    @168
    wceq
    @162
    @142
    vf
    vg
    @35
    @35
    @47
    cB
    cB
    @167
    @160
    @160
    @120
    @47
    @167
    wceq
    @141
    @120
    vx
    @30
    @46
    cI
    @166
    @140
    @120
    @45
    @165
    @37
    @39
    @120
    @32
    @134
    cplusg
    @138
    fveq2d
    oveqd
    mpteq12dv
    adantr
    mpt2eq123dv
    adantr
    wph
    c.pl
    @168
    wceq
    @117
    @118
    @141
    @162
    prdsval.a
    ad4antr
    eqtr4d
    opeq2d
    @163
    @53
    c.xp
    @4
    @163
    @53
    vf
    vg
    cB
    cB
    vx
    cI
    @37
    @39
    @134
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    c.xp
    @142
    @53
    @172
    wceq
    @162
    @142
    vf
    vg
    @35
    @35
    @52
    cB
    cB
    @171
    @160
    @160
    @120
    @52
    @171
    wceq
    @141
    @120
    vx
    @30
    @51
    cI
    @170
    @140
    @120
    @50
    @169
    @37
    @39
    @120
    @32
    @134
    cmulr
    @138
    fveq2d
    oveqd
    mpteq12dv
    adantr
    mpt2eq123dv
    adantr
    wph
    c.xp
    @172
    wceq
    @117
    @118
    @141
    @162
    prdsval.t
    ad4antr
    eqtr4d
    opeq2d
    tpeq123d
    @163
    @57
    @8
    @63
    @10
    @69
    @12
    @163
    @56
    cS
    @7
    wph
    @117
    @118
    @141
    @162
    simp-4r
    opeq2d
    @163
    @62
    c.x
    @9
    @163
    @62
    vf
    vg
    cK
    cB
    vx
    cI
    @36
    @39
    @134
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    c.x
    @142
    @62
    @176
    wceq
    @162
    @142
    vf
    vg
    @58
    @35
    @61
    cK
    cB
    @175
    @142
    @58
    cS
    cbs
    cfv
    cK
    @142
    @56
    cS
    cbs
    wph
    @117
    @118
    @141
    simpllr
    #
    fveq2d
    prdsval.k
    syl6eqr
    @160
    @120
    @61
    @175
    wceq
    @141
    @120
    vx
    @30
    @60
    cI
    @174
    @140
    @120
    @59
    @173
    @36
    @39
    @120
    @32
    @134
    cvsca
    @138
    fveq2d
    oveqd
    mpteq12dv
    adantr
    mpt2eq123dv
    adantr
    wph
    c.x
    @176
    wceq
    @117
    @118
    @141
    @162
    prdsval.m
    ad4antr
    eqtr4d
    opeq2d
    @163
    @68
    c.xi
    @11
    @163
    @68
    vf
    vg
    cB
    cB
    cS
    vx
    cI
    @37
    @39
    @134
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    c.xi
    @142
    @68
    @182
    wceq
    @162
    @142
    vf
    vg
    @35
    @35
    @67
    cB
    cB
    @181
    @160
    @160
    @142
    @56
    cS
    @66
    @180
    cgsu
    @177
    @120
    @66
    @180
    wceq
    @141
    @120
    vx
    @30
    @65
    cI
    @179
    @140
    @120
    @64
    @178
    @37
    @39
    @120
    @32
    @134
    cip
    @138
    fveq2d
    oveqd
    mpteq12dv
    adantr
    oveq12d
    mpt2eq123dv
    adantr
    wph
    c.xi
    @182
    wceq
    @117
    @118
    @141
    @162
    prdsval.j
    ad4antr
    eqtr4d
    opeq2d
    tpeq123d
    uneq12d
    @163
    @92
    @21
    @112
    @26
    @163
    @74
    @16
    @82
    @18
    @91
    @20
    @163
    @73
    cO
    @15
    @163
    @73
    ctopn
    cR
    ccom
    #
    cpt
    cfv
    #
    cO
    @163
    @72
    @183
    cpt
    @163
    @29
    cR
    ctopn
    @119
    @118
    @141
    @162
    simpllr
    coeq2d
    fveq2d
    wph
    cO
    @184
    wceq
    @117
    @118
    @141
    @162
    prdsval.o
    ad4antr
    eqtr4d
    opeq2d
    @163
    @81
    c.le
    @17
    @163
    @81
    @75
    cB
    wss
    #
    @37
    @39
    @134
    cple
    cfv
    #
    wbr
    #
    vx
    cI
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    c.le
    @142
    @81
    @190
    wceq
    @162
    @142
    @80
    @189
    vf
    vg
    @142
    @76
    @185
    @79
    @188
    @142
    @35
    cB
    @75
    @160
    sseq2d
    @120
    @79
    @188
    wb
    @141
    @120
    @78
    @187
    vx
    @30
    cI
    @140
    @120
    @77
    @186
    @37
    @39
    @120
    @32
    @134
    cple
    @138
    fveq2d
    breqd
    raleqbidv
    adantr
    anbi12d
    opabbidv
    adantr
    wph
    c.le
    @190
    wceq
    @117
    @118
    @141
    @162
    prdsval.l
    ad4antr
    eqtr4d
    opeq2d
    @163
    @90
    cD
    @19
    @163
    @90
    vf
    vg
    cB
    cB
    vx
    cI
    @37
    @39
    @134
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    @87
    cun
    #
    cxr
    clt
    csup
    #
    cmpt2
    #
    cD
    @142
    @90
    @197
    wceq
    @162
    @142
    vf
    vg
    @35
    @35
    @89
    cB
    cB
    @196
    @160
    @160
    @142
    cxr
    @88
    @195
    clt
    @142
    @86
    @194
    @87
    @142
    @85
    @193
    @120
    @85
    @193
    wceq
    @141
    @120
    vx
    @30
    @84
    cI
    @192
    @140
    @120
    @83
    @191
    @37
    @39
    @120
    @32
    @134
    cds
    @138
    fveq2d
    oveqd
    mpteq12dv
    adantr
    rneqd
    uneq1d
    supeq1d
    mpt2eq123dv
    adantr
    wph
    cD
    @197
    wceq
    @117
    @118
    @141
    @162
    prdsval.d
    ad4antr
    eqtr4d
    opeq2d
    tpeq123d
    @163
    @94
    @23
    @111
    @25
    @163
    @93
    cH
    @22
    @142
    @162
    simpr
    #
    opeq2d
    @163
    @110
    c.xb
    @24
    @163
    @110
    va
    vc
    cB
    cB
    cxp
    #
    cB
    vd
    ve
    @96
    @98
    cH
    co
    #
    @97
    cH
    cfv
    #
    vx
    cI
    @101
    @102
    @103
    @104
    @134
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cmpt2
    #
    c.xb
    @163
    va
    vc
    @95
    @35
    @109
    @199
    cB
    @206
    @163
    @35
    cB
    @164
    sqxpeqd
    @164
    @163
    vd
    ve
    @99
    @100
    @108
    @200
    @201
    @205
    @163
    @93
    cH
    @96
    @98
    @198
    oveqd
    @163
    @97
    @93
    cH
    @198
    fveq1d
    @120
    @108
    @205
    wceq
    @141
    @162
    @120
    vx
    @30
    @107
    cI
    @204
    @140
    @120
    @106
    @203
    @101
    @102
    @120
    @105
    @202
    @103
    @104
    @120
    @32
    @134
    cco
    @138
    fveq2d
    oveqd
    oveqd
    mpteq12dv
    ad2antrr
    mpt2eq123dv
    mpt2eq123dv
    wph
    c.xb
    @207
    wceq
    @117
    @118
    @141
    @162
    prdsval.x
    ad4antr
    eqtr4d
    opeq2d
    preq12d
    uneq12d
    uneq12d
    csbied2
    csbied2
    anasss
    wph
    cS
    cW
    wcel
    cS
    cvv
    wcel
    prdsval.s
    cS
    cW
    elex
    syl
    wph
    cR
    cZ
    wcel
    cR
    cvv
    wcel
    prdsval.r
    cR
    cZ
    elex
    syl
    @28
    cvv
    wcel
    wph
    @14
    @27
    @6
    @13
    @1
    @3
    @5
    tpex
    @8
    @10
    @12
    tpex
    unex
    @21
    @26
    @16
    @18
    @20
    tpex
    @23
    @25
    prex
    unex
    unex
    a1i
    ovmpt2d
    syl5eq
end
