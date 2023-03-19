include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "cr.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "wiso.mm"
include "fourierdlem54.mm"
include "simpld.mm"
include "simprd.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "elmapi.mm"
include "fzofzp1.mm"
include "ffvelrnd.mm"
include "fourierdlem11.mm"
include "simp2d.mm"
include "resubcld.mm"
include "simp1d.mm"
include "syl5eqel.mm"
include "simp3d.mm"
include "posdifd.mm"
include "syl6breqr.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "readdcld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "cpr.mm"
include "crn.mm"
include "cz.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
include "adantr.mm"
include "cioc.mm"
include "cxr.mm"
include "wss.mm"
include "rexrd.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "fourierdlem4.mm"
include "cle.mm"
include "cico.mm"
include "w3a.mm"
include "elfzofz.mm"
include "elico2.mm"
include "sseldd.mm"
include "icossicc.mm"
include "fourierdlem15.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "elicc2.mm"
include "elrpd.mm"
include "ltaddrpd.mm"
include "recnd.mm"
include "subsub3d.mm"
include "addcomd.mm"
include "addsubassd.mm"
include "3eqtrrd.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "ltled.mm"
include "fourierdlem7.mm"
include "lesub2dd.mm"
include "cc.mm"
include "subsubd.mm"
include "subcld.mm"
include "eqtrd.mm"
include "simpr.mm"
include "sublt0d.mm"
include "mpbird.mm"
include "ltaddneg.mm"
include "eqbrtrd.mm"
include "ltletrd.mm"
include "eliccd.mm"
include "pncan2d.mm"
include "divcan4d.mm"
include "3eqtrd.mm"
include "divcan1d.mm"
include "oveq2d.mm"
include "npcand.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvelrn.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elun2.mm"
include "3eltr4g.mm"
include "wn.mm"
include "elfzelz.mm"
include "ad2antlr.mm"
include "elfzoelz.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "isorel.mm"
include "syl12anc.mm"
include "adantrr.mm"
include "adantrl.mm"
include "btwnnz.mm"
include "syl3anc.mm"
include "pm2.65da.mm"
include "adantlr.mm"
include "ffvelrnda.mm"
include "eqcom.mm"
include "biimpri.mm"
include "adantllr.mm"
include "syl5eqbr.mm"
include "jca.mm"
include "mtand.mm"
include "nrexdv.mm"
include "wfo.mm"
include "wf1o.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "foelrn.mm"
include "sylan.mm"
include "rexbii.mm"
include "sylib.mm"
include "nltled.mm"

theorem fourierdlem63
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vj: setvar j
  assume fourierdlem63.t: |- T = ( B - A )
  assume fourierdlem63.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem63.m: |- ( ph -> M e. NN )
  assume fourierdlem63.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem63.c: |- ( ph -> C e. RR )
  assume fourierdlem63.d: |- ( ph -> D e. RR )
  assume fourierdlem63.cltd: |- ( ph -> C < D )
  assume fourierdlem63.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = C /\ ( p ` m ) = D ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem63.h: |- H = ( { C , D } u. { x e. ( C [,] D ) | E. k e. ZZ ( x + ( k x. T ) ) e. ran Q } )
  assume fourierdlem63.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem63.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )
  assume fourierdlem63.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem63.k: |- ( ph -> K e. ( 0 ... M ) )
  assume fourierdlem63.j: |- ( ph -> J e. ( 0 ..^ N ) )
  assume fourierdlem63.y: |- ( ph -> Y e. ( ( S ` J ) [,) ( S ` ( J + 1 ) ) ) )
  assume fourierdlem63.eyltqk: |- ( ph -> ( E ` Y ) < ( Q ` K ) )
  assume fourierdlem63.x: |- X = ( ( Q ` K ) - ( ( E ` Y ) - Y ) )

  disjoint A i
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint A x
  disjoint i x
  disjoint B i
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint C i
  disjoint C m
  disjoint C p
  disjoint C x
  disjoint D i
  disjoint D m
  disjoint D p
  disjoint D x
  disjoint E k
  disjoint E x
  disjoint k x
  disjoint H f
  disjoint H x
  disjoint J k
  disjoint J x
  disjoint K k
  disjoint K x
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint N f
  disjoint N i
  disjoint N m
  disjoint N p
  disjoint N x
  disjoint Q i
  disjoint Q k
  disjoint Q x
  disjoint i k
  disjoint Q p
  disjoint S f
  disjoint S i
  disjoint S k
  disjoint S x
  disjoint S p
  disjoint T i
  disjoint T k
  disjoint T x
  disjoint Y k
  disjoint Y x
  disjoint f ph
  disjoint i ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint E j
  disjoint H j
  disjoint J j
  disjoint K j
  disjoint N j
  disjoint Q j
  disjoint S j
  disjoint X j
  disjoint j ph
  assert |- ( ph -> ( E ` ( S ` ( J + 1 ) ) ) <_ ( Q ` K ) )

  proof
    wph
    cJ
    c1
    caddc
    co
    #
    cS
    cfv
    #
    cE
    cfv
    #
    cK
    cQ
    cfv
    #
    wph
    @2
    @1
    cB
    @1
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cr
    wph
    vx
    @1
    vx
    cv
    #
    cB
    @9
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @8
    cr
    cE
    cr
    cE
    vx
    cr
    @14
    cmpt
    wceq
    wph
    fourierdlem63.e
    a1i
    #
    @9
    @1
    wceq
    #
    @14
    @8
    wceq
    wph
    @16
    @9
    @1
    @13
    @7
    caddc
    @16
    id
    @16
    @12
    @6
    cT
    cmul
    @16
    @11
    @5
    cfl
    @16
    @10
    @4
    cT
    cdiv
    @9
    @1
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    wph
    cc0
    cN
    cfz
    co
    #
    cr
    @0
    cS
    wph
    cS
    cr
    @17
    cmap
    co
    wcel
    #
    @17
    cr
    cS
    wf
    wph
    @18
    cc0
    cS
    cfv
    cC
    wceq
    cN
    cS
    cfv
    cD
    wceq
    wa
    vi
    cv
    #
    cS
    cfv
    @19
    c1
    caddc
    co
    #
    cS
    cfv
    clt
    wbr
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    wa
    #
    wph
    cS
    cN
    cO
    cfv
    wcel
    #
    @18
    @22
    wa
    #
    wph
    cN
    cn
    wcel
    #
    @23
    wph
    @25
    @23
    wa
    #
    @17
    cH
    clt
    clt
    cS
    wiso
    #
    wph
    vx
    cA
    cB
    cC
    cD
    cP
    cQ
    cS
    cT
    vf
    vi
    vk
    vm
    cH
    cM
    cN
    cO
    vp
    fourierdlem63.t
    fourierdlem63.p
    fourierdlem63.m
    fourierdlem63.q
    fourierdlem63.c
    fourierdlem63.d
    fourierdlem63.cltd
    fourierdlem63.o
    fourierdlem63.h
    fourierdlem63.n
    fourierdlem63.s
    fourierdlem54
    #
    simpld
    #
    simprd
    #
    wph
    @25
    @23
    @24
    wb
    wph
    @25
    @23
    @29
    simpld
    #
    cC
    cD
    cO
    cS
    vi
    vm
    cN
    vp
    fourierdlem63.o
    fourierdlem2
    syl
    mpbid
    simpld
    cS
    cr
    @17
    elmapi
    syl
    #
    wph
    cJ
    @21
    wcel
    #
    @0
    @17
    wcel
    #
    fourierdlem63.j
    cc0
    cN
    cJ
    fzofzp1
    syl
    #
    ffvelrnd
    #
    wph
    @1
    @7
    @36
    wph
    @6
    cT
    wph
    @6
    wph
    @5
    wph
    @4
    cT
    wph
    cB
    @1
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem63.p
    fourierdlem63.m
    fourierdlem63.q
    fourierdlem11
    #
    simp2d
    #
    @36
    resubcld
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem63.t
    wph
    cB
    cA
    @41
    wph
    @37
    @38
    @39
    @40
    simp1d
    #
    resubcld
    syl5eqel
    #
    wph
    cT
    wph
    cc0
    @42
    cT
    clt
    wph
    @39
    cc0
    @42
    clt
    wbr
    wph
    @37
    @38
    @39
    @40
    simp3d
    #
    wph
    cA
    cB
    @43
    @41
    posdifd
    mpbid
    fourierdlem63.t
    syl6breqr
    gt0ne0d
    #
    redivcld
    flcld
    zred
    @44
    remulcld
    readdcld
    #
    fvmptd
    @47
    eqeltrd
    #
    wph
    cc0
    cM
    cfz
    co
    #
    cr
    cK
    cQ
    wph
    cQ
    cr
    @49
    cmap
    co
    wcel
    #
    @49
    cr
    cQ
    wf
    #
    wph
    @50
    cc0
    cQ
    cfv
    cA
    wceq
    cM
    cQ
    cfv
    cB
    wceq
    wa
    @19
    cQ
    cfv
    @20
    cQ
    cfv
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    wral
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @50
    @52
    wa
    #
    fourierdlem63.q
    wph
    cM
    cn
    wcel
    @53
    @54
    wb
    fourierdlem63.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem63.p
    fourierdlem2
    syl
    mpbid
    simpld
    cQ
    cr
    @49
    elmapi
    syl
    #
    fourierdlem63.k
    ffvelrnd
    #
    wph
    @3
    @2
    clt
    wbr
    #
    cX
    cH
    wcel
    #
    wph
    @57
    wa
    #
    @3
    cY
    cE
    cfv
    #
    cY
    cmin
    co
    #
    cmin
    co
    #
    cC
    cD
    cpr
    #
    @9
    vk
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cQ
    crn
    #
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    cC
    cD
    cicc
    co
    #
    crab
    #
    cun
    #
    cX
    cH
    @59
    @62
    @71
    wcel
    #
    @62
    @72
    wcel
    @59
    @62
    @70
    wcel
    @62
    @65
    caddc
    co
    #
    @67
    wcel
    #
    vk
    cz
    wrex
    #
    @73
    @59
    cC
    cD
    @62
    wph
    cC
    cr
    wcel
    #
    @57
    fourierdlem63.c
    adantr
    wph
    cD
    cr
    wcel
    #
    @57
    fourierdlem63.d
    adantr
    #
    wph
    @62
    cr
    wcel
    @57
    wph
    @3
    @61
    @56
    wph
    @60
    cY
    wph
    cA
    cB
    cioc
    co
    #
    cr
    @60
    wph
    cA
    cxr
    wcel
    @38
    @80
    cr
    wss
    wph
    cA
    @43
    rexrd
    @41
    cA
    cB
    iocssre
    syl2anc
    wph
    cr
    @80
    cY
    cE
    wph
    vx
    cA
    cB
    cT
    cE
    @43
    @41
    @45
    fourierdlem63.t
    fourierdlem63.e
    fourierdlem4
    wph
    cY
    cr
    wcel
    #
    cJ
    cS
    cfv
    #
    cY
    cle
    wbr
    #
    cY
    @1
    clt
    wbr
    #
    wph
    cY
    @82
    @1
    cico
    co
    #
    wcel
    #
    @81
    @83
    @84
    w3a
    #
    fourierdlem63.y
    wph
    @82
    cr
    wcel
    #
    @1
    cxr
    wcel
    @86
    @87
    wb
    wph
    @17
    cr
    cJ
    cS
    @32
    wph
    @33
    cJ
    @17
    wcel
    #
    fourierdlem63.j
    cJ
    cc0
    cN
    elfzofz
    syl
    #
    ffvelrnd
    #
    wph
    @1
    @36
    rexrd
    @82
    @1
    cY
    elico2
    syl2anc
    mpbid
    #
    simp1d
    #
    ffvelrnd
    sseldd
    #
    @93
    resubcld
    #
    resubcld
    #
    adantr
    #
    wph
    cC
    @62
    cle
    wbr
    @57
    wph
    cC
    @62
    fourierdlem63.c
    @96
    wph
    cC
    cY
    @62
    fourierdlem63.c
    @93
    @96
    wph
    @81
    cC
    cY
    cle
    wbr
    #
    cY
    cD
    cle
    wbr
    #
    wph
    cY
    @70
    wcel
    #
    @81
    @98
    @99
    w3a
    #
    wph
    @85
    @70
    cY
    wph
    @85
    @82
    @1
    cicc
    co
    @70
    @82
    @1
    icossicc
    wph
    cC
    cD
    cS
    cJ
    cN
    wph
    cC
    fourierdlem63.c
    rexrd
    wph
    cD
    fourierdlem63.d
    rexrd
    wph
    cC
    cD
    cO
    cS
    vi
    vm
    cN
    vp
    fourierdlem63.o
    @31
    @30
    fourierdlem15
    #
    fourierdlem63.j
    fourierdlem8
    syl5ss
    fourierdlem63.y
    sseldd
    wph
    @77
    @78
    @100
    @101
    wb
    fourierdlem63.c
    fourierdlem63.d
    cC
    cD
    cY
    elicc2
    syl2anc
    mpbid
    simp2d
    wph
    cY
    cY
    @3
    @60
    cmin
    co
    #
    caddc
    co
    #
    @62
    clt
    wph
    cY
    @103
    @93
    wph
    @103
    wph
    @3
    @60
    @56
    @94
    resubcld
    wph
    @60
    @3
    clt
    wbr
    cc0
    @103
    clt
    wbr
    fourierdlem63.eyltqk
    wph
    @60
    @3
    @94
    @56
    posdifd
    mpbid
    elrpd
    ltaddrpd
    wph
    @62
    @3
    cY
    caddc
    co
    #
    @60
    cmin
    co
    cY
    @3
    caddc
    co
    #
    @60
    cmin
    co
    @104
    wph
    @3
    @60
    cY
    wph
    @3
    @56
    recnd
    #
    wph
    @60
    @94
    recnd
    #
    wph
    cY
    @93
    recnd
    #
    subsub3d
    wph
    @105
    @106
    @60
    cmin
    wph
    @3
    cY
    @107
    @109
    addcomd
    oveq1d
    wph
    cY
    @3
    @60
    @109
    @107
    @108
    addsubassd
    3eqtrrd
    breqtrd
    #
    lelttrd
    ltled
    adantr
    @59
    @62
    cD
    @97
    @79
    @59
    @62
    @1
    cD
    @97
    wph
    @1
    cr
    wcel
    #
    @57
    @36
    adantr
    #
    @79
    @59
    @62
    @3
    @2
    @1
    cmin
    co
    #
    cmin
    co
    #
    @1
    @97
    @59
    @3
    @113
    wph
    @3
    cr
    wcel
    @57
    @56
    adantr
    #
    wph
    @113
    cr
    wcel
    @57
    wph
    @2
    @1
    @48
    @36
    resubcld
    #
    adantr
    resubcld
    @112
    wph
    @62
    @114
    cle
    wbr
    @57
    wph
    @113
    @61
    @3
    @116
    @95
    @56
    wph
    vx
    cA
    cB
    cT
    cE
    cY
    @1
    @43
    @41
    @45
    fourierdlem63.t
    fourierdlem63.e
    @93
    @36
    wph
    cY
    @1
    @93
    @36
    wph
    @81
    @83
    @84
    @92
    simp3d
    ltled
    fourierdlem7
    lesub2dd
    adantr
    @59
    @114
    @1
    @3
    @2
    cmin
    co
    #
    caddc
    co
    #
    @1
    clt
    @59
    @114
    @117
    @1
    caddc
    co
    #
    @118
    @59
    @3
    @2
    @1
    wph
    @3
    cc
    wcel
    @57
    @107
    adantr
    wph
    @2
    cc
    wcel
    @57
    wph
    @2
    @48
    recnd
    #
    adantr
    @59
    @1
    @112
    recnd
    subsubd
    wph
    @119
    @118
    wceq
    @57
    wph
    @117
    @1
    wph
    @3
    @2
    @107
    @120
    subcld
    wph
    @1
    @36
    recnd
    addcomd
    adantr
    eqtrd
    @59
    @117
    cc0
    clt
    wbr
    #
    @118
    @1
    clt
    wbr
    #
    @59
    @121
    @57
    wph
    @57
    simpr
    @59
    @3
    @2
    @115
    wph
    @2
    cr
    wcel
    @57
    @48
    adantr
    #
    sublt0d
    mpbird
    @59
    @117
    cr
    wcel
    @111
    @121
    @122
    wb
    @59
    @3
    @2
    @115
    @123
    resubcld
    @112
    @117
    @1
    ltaddneg
    syl2anc
    mpbid
    eqbrtrd
    lelttrd
    #
    wph
    @1
    cD
    cle
    wbr
    #
    @57
    wph
    @111
    cC
    @1
    cle
    wbr
    #
    @125
    wph
    @1
    @70
    wcel
    #
    @111
    @126
    @125
    w3a
    #
    wph
    @17
    @70
    @0
    cS
    @102
    @35
    ffvelrnd
    wph
    @77
    @78
    @127
    @128
    wb
    fourierdlem63.c
    fourierdlem63.d
    cC
    cD
    @1
    elicc2
    syl2anc
    mpbid
    simp3d
    adantr
    ltletrd
    ltled
    eliccd
    wph
    @76
    @57
    wph
    @61
    cT
    cdiv
    co
    #
    cz
    wcel
    @62
    @129
    cT
    cmul
    co
    #
    caddc
    co
    #
    @67
    wcel
    #
    @76
    wph
    @129
    cB
    cY
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wph
    @129
    cY
    @135
    cT
    cmul
    co
    #
    caddc
    co
    #
    cY
    cmin
    co
    #
    cT
    cdiv
    co
    @136
    cT
    cdiv
    co
    @135
    wph
    @61
    @138
    cT
    cdiv
    wph
    @60
    @137
    cY
    cmin
    wph
    vx
    cY
    @14
    @137
    cr
    cE
    cr
    @15
    @9
    cY
    wceq
    #
    @14
    @137
    wceq
    wph
    @139
    @9
    cY
    @13
    @136
    caddc
    @139
    id
    @139
    @12
    @135
    cT
    cmul
    @139
    @11
    @134
    cfl
    @139
    @10
    @133
    cT
    cdiv
    @9
    cY
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    @93
    wph
    cY
    @136
    @93
    wph
    @135
    cT
    wph
    @135
    wph
    @134
    wph
    @133
    cT
    wph
    cB
    cY
    @41
    @93
    resubcld
    @44
    @46
    redivcld
    flcld
    #
    zred
    #
    @44
    remulcld
    #
    readdcld
    fvmptd
    oveq1d
    oveq1d
    wph
    @138
    @136
    cT
    cdiv
    wph
    cY
    @136
    @109
    wph
    @136
    @142
    recnd
    pncan2d
    oveq1d
    wph
    @135
    cT
    wph
    @135
    @141
    recnd
    wph
    cT
    @44
    recnd
    #
    @46
    divcan4d
    3eqtrd
    @140
    eqeltrd
    wph
    @131
    @3
    @67
    wph
    @131
    @62
    @61
    caddc
    co
    @3
    wph
    @130
    @61
    @62
    caddc
    wph
    @61
    cT
    wph
    @61
    @95
    recnd
    #
    @143
    @46
    divcan1d
    oveq2d
    wph
    @3
    @61
    @107
    @144
    npcand
    eqtrd
    wph
    cQ
    wfun
    #
    cK
    cQ
    cdm
    #
    wcel
    @3
    @67
    wcel
    wph
    @51
    @145
    @55
    @49
    cr
    cQ
    ffun
    syl
    wph
    cK
    @49
    @146
    fourierdlem63.k
    wph
    @51
    @146
    @49
    wceq
    @55
    @49
    cr
    cQ
    fdm
    syl
    eleqtrrd
    cK
    cQ
    fvelrn
    syl2anc
    eqeltrd
    @75
    @132
    vk
    @129
    cz
    @64
    @129
    wceq
    #
    @74
    @131
    @67
    @147
    @65
    @130
    @62
    caddc
    @64
    @129
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    rspcev
    syl2anc
    adantr
    @69
    @76
    vx
    @62
    @70
    @9
    @62
    wceq
    #
    @68
    @75
    vk
    cz
    @148
    @66
    @74
    @67
    @9
    @62
    @65
    caddc
    oveq1
    eleq1d
    rexbidv
    elrab
    sylanbrc
    @62
    @71
    @63
    elun2
    syl
    fourierdlem63.x
    fourierdlem63.h
    3eltr4g
    @59
    @58
    vj
    cv
    #
    cS
    cfv
    #
    cX
    wceq
    #
    vj
    @17
    wrex
    #
    @59
    @151
    vj
    @17
    @59
    @149
    @17
    wcel
    #
    wa
    #
    @151
    @82
    @150
    clt
    wbr
    #
    @150
    @1
    clt
    wbr
    #
    wa
    #
    wph
    @153
    @157
    wn
    @57
    wph
    @153
    wa
    #
    @157
    @149
    cz
    wcel
    #
    @153
    @159
    wph
    @157
    @149
    cc0
    cN
    elfzelz
    ad2antlr
    @158
    @157
    wa
    cJ
    cz
    wcel
    #
    cJ
    @149
    clt
    wbr
    #
    @149
    @0
    clt
    wbr
    #
    @159
    wn
    wph
    @160
    @153
    @157
    wph
    @33
    @160
    fourierdlem63.j
    cJ
    cc0
    cN
    elfzoelz
    syl
    ad2antrr
    @158
    @155
    @161
    @156
    @158
    @155
    wa
    #
    @161
    @155
    @158
    @155
    simpr
    @163
    @27
    @89
    @153
    @161
    @155
    wb
    wph
    @27
    @153
    @155
    wph
    @26
    @27
    @28
    simprd
    #
    ad2antrr
    wph
    @89
    @153
    @155
    @90
    ad2antrr
    wph
    @153
    @155
    simplr
    @17
    cH
    cJ
    @149
    clt
    clt
    cS
    isorel
    syl12anc
    mpbird
    adantrr
    @158
    @156
    @162
    @155
    @158
    @156
    wa
    #
    @162
    @156
    @158
    @156
    simpr
    @165
    @27
    @153
    @34
    @162
    @156
    wb
    wph
    @27
    @153
    @156
    @164
    ad2antrr
    wph
    @153
    @156
    simplr
    wph
    @34
    @153
    @156
    @35
    ad2antrr
    @17
    cH
    @149
    @0
    clt
    clt
    cS
    isorel
    syl12anc
    mpbird
    adantrl
    cJ
    @149
    btwnnz
    syl3anc
    pm2.65da
    adantlr
    @154
    @151
    wa
    @155
    @156
    wph
    @153
    @151
    @155
    @57
    @158
    @151
    wa
    @82
    cY
    @150
    wph
    @88
    @153
    @151
    @91
    ad2antrr
    wph
    @81
    @153
    @151
    @93
    ad2antrr
    @158
    @150
    cr
    wcel
    @151
    wph
    @17
    cr
    @149
    cS
    @32
    ffvelrnda
    adantr
    wph
    @83
    @153
    @151
    wph
    @81
    @83
    @84
    @92
    simp2d
    ad2antrr
    wph
    @151
    cY
    @150
    clt
    wbr
    @153
    wph
    @151
    wa
    cY
    cX
    @150
    clt
    wph
    cY
    cX
    clt
    wbr
    @151
    wph
    cY
    @62
    cX
    clt
    @110
    fourierdlem63.x
    syl6breqr
    adantr
    @151
    cX
    @150
    wceq
    #
    wph
    @166
    @151
    cX
    @150
    eqcom
    #
    biimpri
    adantl
    breqtrd
    adantlr
    lelttrd
    adantllr
    @59
    @151
    @156
    @153
    @59
    @151
    wa
    @150
    cX
    @1
    clt
    @59
    @151
    simpr
    @59
    cX
    @1
    clt
    wbr
    @151
    @59
    cX
    @62
    @1
    clt
    fourierdlem63.x
    @124
    syl5eqbr
    adantr
    eqbrtrd
    adantlr
    jca
    mtand
    nrexdv
    wph
    @58
    @152
    @57
    wph
    @58
    wa
    @166
    vj
    @17
    wrex
    #
    @152
    wph
    @17
    cH
    cS
    wfo
    #
    @58
    @168
    wph
    @17
    cH
    cS
    wf1o
    #
    @169
    wph
    @27
    @170
    @164
    @17
    cH
    clt
    clt
    cS
    isof1o
    syl
    @17
    cH
    cS
    f1ofo
    syl
    vj
    @17
    cH
    cX
    cS
    foelrn
    sylan
    @166
    @151
    vj
    @17
    @167
    rexbii
    sylib
    adantlr
    mtand
    pm2.65da
    nltled
end
