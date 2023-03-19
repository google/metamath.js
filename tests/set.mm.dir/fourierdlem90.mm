include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cioo.mm"
include "cc.mm"
include "ccncf.mm"
include "cres.mm"
include "cicc.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "fourierdlem11.mm"
include "simp1d.mm"
include "simp2d.mm"
include "iccssred.mm"
include "cioc.mm"
include "simp3d.mm"
include "fourierdlem17.mm"
include "fourierdlem4.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wf.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "wiso.mm"
include "cpnf.mm"
include "elioore.mm"
include "syl.mm"
include "cxr.mm"
include "w3a.mm"
include "elioo4g.mm"
include "sylib.mm"
include "simprd.mm"
include "simpld.mm"
include "fourierdlem54.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "mpbid.mm"
include "elmapi.mm"
include "elfzofz.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "wss.mm"
include "rexrd.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "fzofzp1.mm"
include "eqid.mm"
include "cmin.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "c2.mm"
include "cdiv.mm"
include "cif.mm"
include "cpr.mm"
include "cmul.mm"
include "crn.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "cun.mm"
include "oveq2i.mm"
include "eleq1i.mm"
include "rexbii.mm"
include "a1i.mm"
include "rabbiia.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "id.mm"
include "eqcomi.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "fourierdlem79.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "mpdan.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "cle.mm"
include "csup.mm"
include "fourierdlem37.mm"
include "ancli.mm"
include "reseq2d.mm"
include "eleq12d.mm"
include "sylc.mm"
include "rescncf.mm"
include "eqeltrd.mm"
include "cncfshiftioo.mm"
include "cmpt.mm"
include "eqeq12d.mm"
include "chash.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "cio.mm"
include "isoeq5.mm"
include "ax-mp.mm"
include "iotabii.mm"
include "fourierdlem65.mm"
include "recnd.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "fourierdlem15.mm"
include "subcld.mm"
include "subsub23d.mm"
include "mpbird.mm"
include "addsub12d.mm"
include "sub32d.mm"
include "subidd.mm"
include "cneg.mm"
include "df-neg.mm"
include "negsubdi2d.mm"
include "syl5eqr.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "pncan3d.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "ioossre.mm"
include "resmptd.mm"
include "fveq1i.mm"
include "adantr.mm"
include "sselda.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "npcand.mm"
include "3brtr4d.mm"
include "ltadd1d.mm"
include "iooltub.mm"
include "eliood.mm"
include "fvres.mm"
include "subsub2d.mm"
include "wne.mm"
include "posdifd.mm"
include "syl6breqr.mm"
include "gt0ne0d.mm"
include "divcan1d.mm"
include "cfl.mm"
include "oveq2.mm"
include "adantl.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "readdcld.mm"
include "fvmptd.mm"
include "mulcld.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "divcan4d.mm"
include "adantlr.mm"
include "fperiodmul.mm"
include "3eqtrrd.mm"
include "mpteq2dva.mm"
include "3eltr3d.mm"

theorem fourierdlem90
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vj: setvar j
  assume fourierdlem90.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem90.t: |- T = ( B - A )
  assume fourierdlem90.m: |- ( ph -> M e. NN )
  assume fourierdlem90.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem90.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem90.6: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem90.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem90.c: |- ( ph -> C e. RR )
  assume fourierdlem90.d: |- ( ph -> D e. ( C (,) +oo ) )
  assume fourierdlem90.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = C /\ ( p ` m ) = D ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem90.h: |- H = ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } )
  assume fourierdlem90.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem90.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )
  assume fourierdlem90.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem90.J: |- L = ( y e. ( A (,] B ) |-> if ( y = B , A , y ) )
  assume fourierdlem90.17: |- ( ph -> J e. ( 0 ..^ N ) )
  assume fourierdlem90.u: |- U = ( ( S ` ( J + 1 ) ) - ( E ` ( S ` ( J + 1 ) ) ) )
  assume fourierdlem90.g: |- G = ( F |` ( ( L ` ( E ` ( S ` J ) ) ) (,) ( E ` ( S ` ( J + 1 ) ) ) ) )
  assume fourierdlem90.r: |- R = ( y e. ( ( ( L ` ( E ` ( S ` J ) ) ) + U ) (,) ( ( E ` ( S ` ( J + 1 ) ) ) + U ) ) |-> ( G ` ( y - U ) ) )
  assume fourierdlem90.i: |- I = ( x e. RR |-> sup ( { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( L ` ( E ` x ) ) } , RR , < ) )

  disjoint A f
  disjoint A k
  disjoint A y
  disjoint f k
  disjoint f y
  disjoint k y
  disjoint A i
  disjoint A x
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint x y
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B f
  disjoint B k
  disjoint B y
  disjoint B i
  disjoint B x
  disjoint B m
  disjoint B p
  disjoint C f
  disjoint C y
  disjoint C i
  disjoint C m
  disjoint C p
  disjoint C x
  disjoint D f
  disjoint D y
  disjoint D i
  disjoint D m
  disjoint D p
  disjoint D x
  disjoint E f
  disjoint E k
  disjoint E y
  disjoint E i
  disjoint E x
  disjoint F i
  disjoint F x
  disjoint F y
  disjoint G y
  disjoint H f
  disjoint H y
  disjoint H x
  disjoint I f
  disjoint I k
  disjoint I i
  disjoint I x
  disjoint J i
  disjoint J x
  disjoint J y
  disjoint L i
  disjoint L x
  disjoint L y
  disjoint M i
  disjoint M x
  disjoint M m
  disjoint M p
  disjoint N f
  disjoint N k
  disjoint N y
  disjoint N i
  disjoint N x
  disjoint N m
  disjoint N p
  disjoint Q f
  disjoint Q k
  disjoint Q y
  disjoint Q i
  disjoint Q x
  disjoint Q p
  disjoint S f
  disjoint S k
  disjoint S y
  disjoint S i
  disjoint S x
  disjoint S p
  disjoint T i
  disjoint T k
  disjoint T x
  disjoint T y
  disjoint U y
  disjoint f ph
  disjoint k ph
  disjoint ph y
  disjoint i ph
  disjoint ph x
  disjoint k x
  disjoint A j
  disjoint f j
  disjoint j k
  disjoint j y
  disjoint i j
  disjoint j x
  disjoint E j
  disjoint I j
  disjoint J j
  disjoint L j
  disjoint M j
  disjoint N j
  disjoint Q j
  disjoint S j
  disjoint j ph
  assert |- ( ph -> ( F |` ( ( S ` J ) (,) ( S ` ( J + 1 ) ) ) ) e. ( ( ( S ` J ) (,) ( S ` ( J + 1 ) ) ) -cn-> CC ) )

  proof
    wph
    cR
    cJ
    cS
    cfv
    #
    cE
    cfv
    #
    cL
    cfv
    #
    cU
    caddc
    co
    #
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
    cU
    caddc
    co
    #
    cioo
    co
    #
    cc
    ccncf
    co
    cF
    @0
    @5
    cioo
    co
    #
    cres
    #
    @9
    cc
    ccncf
    co
    wph
    vy
    @2
    @6
    @2
    @6
    cioo
    co
    #
    @8
    cU
    cG
    cR
    wph
    cA
    cB
    cicc
    co
    #
    cr
    @2
    wph
    cA
    cB
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
    fourierdlem90.p
    fourierdlem90.m
    fourierdlem90.q
    fourierdlem11
    #
    simp1d
    #
    wph
    @13
    @14
    @15
    @16
    simp2d
    #
    iccssred
    wph
    cA
    cB
    cioc
    co
    #
    @12
    @1
    cL
    wph
    vy
    cA
    cB
    cL
    @17
    @18
    wph
    @13
    @14
    @15
    @16
    simp3d
    #
    fourierdlem90.J
    fourierdlem17
    wph
    cr
    @19
    @0
    cE
    wph
    vx
    cA
    cB
    cT
    cE
    @17
    @18
    @20
    fourierdlem90.t
    fourierdlem90.e
    fourierdlem4
    #
    wph
    cc0
    cN
    cfz
    co
    #
    cr
    cJ
    cS
    wph
    cS
    cr
    @22
    cmap
    co
    wcel
    #
    @22
    cr
    cS
    wf
    wph
    @23
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
    @24
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
    @23
    @27
    wa
    #
    wph
    cN
    cn
    wcel
    #
    @28
    wph
    @30
    @28
    wa
    @22
    cH
    clt
    clt
    cS
    wiso
    wph
    vy
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
    fourierdlem90.t
    fourierdlem90.p
    fourierdlem90.m
    fourierdlem90.q
    fourierdlem90.c
    wph
    cD
    cC
    cpnf
    cioo
    co
    wcel
    #
    cD
    cr
    wcel
    #
    fourierdlem90.d
    cD
    cC
    cpnf
    elioore
    syl
    #
    wph
    cC
    cD
    clt
    wbr
    #
    cD
    cpnf
    clt
    wbr
    #
    wph
    cC
    cxr
    wcel
    cpnf
    cxr
    wcel
    @32
    w3a
    #
    @34
    @35
    wa
    #
    wph
    @31
    @36
    @37
    wa
    fourierdlem90.d
    cC
    cpnf
    cD
    elioo4g
    sylib
    simprd
    simpld
    #
    fourierdlem90.o
    fourierdlem90.h
    fourierdlem90.n
    fourierdlem90.s
    fourierdlem54
    simpld
    #
    simprd
    #
    wph
    @30
    @28
    @29
    wb
    wph
    @30
    @28
    @39
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
    fourierdlem90.o
    fourierdlem2
    syl
    mpbid
    simpld
    cS
    cr
    @22
    elmapi
    syl
    #
    wph
    cJ
    @26
    wcel
    #
    cJ
    @22
    wcel
    fourierdlem90.17
    cJ
    cc0
    cN
    elfzofz
    syl
    #
    ffvelrnd
    #
    ffvelrnd
    ffvelrnd
    sseldd
    #
    wph
    @19
    cr
    @6
    wph
    cA
    cxr
    wcel
    @14
    @19
    cr
    wss
    wph
    cA
    @17
    rexrd
    @18
    cA
    cB
    iocssre
    syl2anc
    wph
    cr
    @19
    @5
    cE
    @21
    wph
    @22
    cr
    @4
    cS
    @42
    wph
    @43
    @4
    @22
    wcel
    fourierdlem90.17
    cc0
    cN
    cJ
    fzofzp1
    syl
    ffvelrnd
    #
    ffvelrnd
    sseldd
    #
    @11
    eqid
    wph
    cU
    @5
    @6
    cmin
    co
    #
    cr
    fourierdlem90.u
    wph
    @5
    @6
    @47
    @48
    resubcld
    syl5eqel
    #
    @8
    eqid
    wph
    cG
    cF
    @11
    cres
    #
    @11
    cc
    ccncf
    co
    #
    fourierdlem90.g
    wph
    @51
    cF
    @0
    cI
    cfv
    #
    cQ
    cfv
    #
    @53
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @11
    cres
    #
    @52
    wph
    @59
    @51
    wph
    cF
    @11
    @57
    wph
    @43
    @11
    @57
    wss
    #
    fourierdlem90.17
    wph
    @43
    @60
    wph
    vj
    cv
    #
    @26
    wcel
    #
    wa
    #
    @61
    cS
    cfv
    #
    cE
    cfv
    #
    cL
    cfv
    #
    @61
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
    cioo
    co
    #
    @64
    cI
    cfv
    #
    cQ
    cfv
    #
    @71
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wss
    #
    wi
    wph
    @43
    wa
    #
    @60
    wi
    vj
    cJ
    @26
    @61
    cJ
    wceq
    #
    @63
    @77
    @76
    @60
    @78
    @62
    @43
    wph
    @61
    cJ
    @26
    eleq1
    anbi2d
    #
    @78
    @70
    @11
    @75
    @57
    @78
    @66
    @2
    @69
    @6
    cioo
    @78
    @65
    @1
    cL
    @78
    @64
    @0
    cE
    @61
    cJ
    cS
    fveq2
    #
    fveq2d
    fveq2d
    #
    @78
    @68
    @5
    cE
    @78
    @67
    @4
    cS
    @61
    cJ
    c1
    caddc
    oveq1
    fveq2d
    #
    fveq2d
    #
    oveq12d
    @78
    @72
    @54
    @74
    @56
    cioo
    @78
    @71
    @53
    cQ
    @78
    @64
    @0
    cI
    @80
    fveq2d
    #
    fveq2d
    @78
    @73
    @55
    cQ
    @78
    @71
    @53
    c1
    caddc
    @84
    oveq1d
    fveq2d
    oveq12d
    sseq12d
    imbi12d
    wph
    vx
    vy
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
    vj
    vk
    vm
    cE
    cH
    cI
    cL
    cM
    cN
    cO
    @64
    @68
    @64
    cmin
    co
    #
    c1
    cQ
    cfv
    cA
    cmin
    co
    #
    clt
    wbr
    @85
    c2
    cdiv
    co
    @86
    c2
    cdiv
    co
    cif
    caddc
    co
    #
    vp
    fourierdlem90.t
    fourierdlem90.p
    fourierdlem90.m
    fourierdlem90.q
    fourierdlem90.c
    @33
    @38
    fourierdlem90.o
    cH
    cC
    cD
    cpr
    #
    vy
    cv
    #
    vk
    cv
    #
    cB
    cA
    cmin
    co
    #
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
    vy
    cC
    cD
    cicc
    co
    #
    crab
    #
    cun
    #
    @88
    vx
    cv
    #
    @90
    cT
    cmul
    co
    #
    caddc
    co
    #
    @94
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    @97
    crab
    #
    cun
    cH
    @88
    @89
    @101
    caddc
    co
    #
    @94
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @97
    crab
    #
    cun
    @99
    fourierdlem90.h
    @109
    @98
    @88
    @108
    @96
    vy
    @97
    @108
    @96
    wb
    @89
    @97
    wcel
    @107
    @95
    vk
    cz
    @106
    @93
    @94
    @101
    @92
    @89
    caddc
    cT
    @91
    @90
    cmul
    fourierdlem90.t
    oveq2i
    oveq2i
    eleq1i
    rexbii
    a1i
    rabbiia
    uneq2i
    eqtri
    #
    @98
    @105
    @88
    @96
    @104
    vy
    vx
    @97
    @89
    @100
    wceq
    #
    @95
    @103
    vk
    cz
    @111
    @93
    @102
    @94
    @111
    @89
    @100
    @92
    @101
    caddc
    @111
    id
    @92
    @101
    wceq
    @111
    @91
    cT
    @90
    cmul
    cT
    @91
    fourierdlem90.t
    eqcomi
    oveq2i
    a1i
    oveq12d
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    eqtri
    fourierdlem90.n
    fourierdlem90.s
    fourierdlem90.e
    fourierdlem90.J
    @87
    eqid
    fourierdlem90.i
    fourierdlem79
    vtoclg
    anabsi7
    mpdan
    #
    resabs1d
    eqcomd
    wph
    @60
    @58
    @57
    cc
    ccncf
    co
    #
    wcel
    #
    @59
    @52
    wcel
    @112
    wph
    @53
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    wph
    @116
    wa
    #
    @114
    wph
    cr
    @115
    @0
    cI
    wph
    cr
    @115
    cI
    wf
    @100
    cr
    wcel
    #
    @24
    cQ
    cfv
    #
    @100
    cE
    cfv
    cL
    cfv
    cle
    wbr
    vi
    @115
    crab
    #
    cr
    clt
    csup
    @120
    wcel
    wi
    wph
    vx
    vy
    cA
    cB
    cP
    cQ
    cT
    vi
    vm
    cE
    cI
    cL
    cM
    vp
    fourierdlem90.p
    fourierdlem90.m
    fourierdlem90.q
    fourierdlem90.t
    fourierdlem90.e
    fourierdlem90.J
    fourierdlem90.i
    fourierdlem37
    simpld
    @45
    ffvelrnd
    #
    wph
    @116
    @121
    ancli
    wph
    @24
    @115
    wcel
    #
    wa
    #
    cF
    @119
    @25
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @125
    cc
    ccncf
    co
    #
    wcel
    #
    wi
    @117
    @114
    wi
    vi
    @53
    @115
    @24
    @53
    wceq
    #
    @123
    @117
    @128
    @114
    @129
    @122
    @116
    wph
    @24
    @53
    @115
    eleq1
    anbi2d
    @129
    @126
    @58
    @127
    @113
    @129
    @125
    @57
    cF
    @129
    @119
    @54
    @124
    @56
    cioo
    @24
    @53
    cQ
    fveq2
    @129
    @25
    @55
    cQ
    @24
    @53
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    #
    reseq2d
    @129
    @125
    @57
    cc
    ccncf
    @130
    oveq1d
    eleq12d
    imbi12d
    fourierdlem90.fcn
    vtoclg
    sylc
    @57
    cc
    @11
    @58
    rescncf
    sylc
    eqeltrd
    syl5eqel
    fourierdlem90.r
    cncfshiftioo
    wph
    cR
    vy
    @8
    @89
    cU
    cmin
    co
    #
    cG
    cfv
    #
    cmpt
    #
    vy
    @9
    @132
    cmpt
    #
    @10
    cR
    @133
    wceq
    wph
    fourierdlem90.r
    a1i
    wph
    vy
    @8
    @9
    @132
    wph
    @3
    @0
    @7
    @5
    cioo
    wph
    @3
    @2
    @49
    caddc
    co
    #
    @6
    @5
    @0
    cmin
    co
    #
    cmin
    co
    #
    @49
    caddc
    co
    #
    @0
    @3
    @135
    wceq
    wph
    cU
    @49
    @2
    caddc
    fourierdlem90.u
    oveq2i
    a1i
    wph
    @2
    @137
    @49
    caddc
    wph
    @137
    @2
    wph
    @137
    @2
    wceq
    @6
    @2
    cmin
    co
    #
    @136
    wceq
    #
    wph
    @43
    @140
    fourierdlem90.17
    wph
    @43
    @140
    @63
    @69
    @66
    cmin
    co
    #
    @85
    wceq
    #
    wi
    @77
    @140
    wi
    vj
    cJ
    @26
    @78
    @63
    @77
    @142
    @140
    @79
    @78
    @141
    @139
    @85
    @136
    @78
    @69
    @6
    @66
    @2
    cmin
    @83
    @81
    oveq12d
    @78
    @68
    @5
    @64
    @0
    cmin
    @82
    @80
    oveq12d
    eqeq12d
    imbi12d
    wph
    vx
    vy
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
    vj
    vk
    vm
    cE
    cL
    cM
    cN
    cO
    @64
    cB
    @65
    cmin
    co
    caddc
    co
    #
    vp
    fourierdlem90.p
    fourierdlem90.t
    fourierdlem90.m
    fourierdlem90.q
    fourierdlem90.c
    fourierdlem90.d
    fourierdlem90.o
    cN
    cH
    chash
    cfv
    #
    c1
    cmin
    co
    @99
    chash
    cfv
    #
    c1
    cmin
    co
    fourierdlem90.n
    @144
    @145
    c1
    cmin
    cH
    @99
    chash
    @110
    fveq2i
    oveq1i
    eqtri
    cS
    @22
    cH
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vf
    cio
    @22
    @99
    clt
    clt
    @146
    wiso
    #
    vf
    cio
    fourierdlem90.s
    @147
    @148
    vf
    cH
    @99
    wceq
    @147
    @148
    wb
    @110
    @22
    cH
    @99
    clt
    clt
    @146
    isoeq5
    ax-mp
    iotabii
    eqtri
    fourierdlem90.e
    fourierdlem90.J
    @143
    eqid
    fourierdlem65
    vtoclg
    anabsi7
    mpdan
    wph
    @6
    @136
    @2
    wph
    @6
    @48
    recnd
    #
    wph
    @5
    @0
    wph
    @5
    @47
    recnd
    #
    wph
    @97
    cc
    @0
    wph
    @97
    cr
    cc
    wph
    cC
    cD
    fourierdlem90.c
    @33
    iccssred
    ax-resscn
    syl6ss
    wph
    @22
    @97
    cJ
    cS
    wph
    cC
    cD
    cO
    cS
    vi
    vm
    cN
    vp
    fourierdlem90.o
    @41
    @40
    fourierdlem15
    @44
    ffvelrnd
    sseldd
    #
    subcld
    #
    wph
    @2
    @46
    recnd
    subsub23d
    mpbird
    eqcomd
    oveq1d
    wph
    @138
    @5
    @137
    @6
    cmin
    co
    #
    caddc
    co
    @5
    @0
    @5
    cmin
    co
    #
    caddc
    co
    @0
    wph
    @137
    @5
    @6
    wph
    @6
    @136
    @149
    @152
    subcld
    @150
    @149
    addsub12d
    wph
    @153
    @154
    @5
    caddc
    wph
    @153
    @6
    @6
    cmin
    co
    #
    @136
    cmin
    co
    cc0
    @136
    cmin
    co
    #
    @154
    wph
    @6
    @136
    @6
    @149
    @152
    @149
    sub32d
    wph
    @155
    cc0
    @136
    cmin
    wph
    @6
    @149
    subidd
    oveq1d
    wph
    @156
    @136
    cneg
    @154
    @136
    df-neg
    wph
    @5
    @0
    @150
    @151
    negsubdi2d
    syl5eqr
    3eqtrd
    oveq2d
    wph
    @5
    @0
    @150
    @151
    pncan3d
    3eqtrd
    3eqtrd
    #
    wph
    @7
    @6
    @49
    caddc
    co
    @5
    cU
    @49
    @6
    caddc
    fourierdlem90.u
    oveq2i
    wph
    @6
    @5
    @149
    @150
    pncan3d
    syl5eq
    #
    oveq12d
    #
    mpteq1d
    wph
    @10
    vy
    cr
    @89
    cF
    cfv
    #
    cmpt
    #
    @9
    cres
    vy
    @9
    @160
    cmpt
    @134
    wph
    cF
    @161
    @9
    wph
    vy
    cr
    cc
    cF
    fourierdlem90.f
    feqmptd
    reseq1d
    wph
    vy
    cr
    @9
    @160
    @9
    cr
    wss
    wph
    @0
    @5
    ioossre
    a1i
    #
    resmptd
    wph
    vy
    @9
    @160
    @132
    wph
    @89
    @9
    wcel
    #
    wa
    #
    @132
    @131
    @51
    cfv
    #
    @131
    cF
    cfv
    #
    @160
    @132
    @165
    wceq
    @164
    @131
    cG
    @51
    fourierdlem90.g
    fveq1i
    a1i
    @164
    @131
    @11
    wcel
    @165
    @166
    wceq
    @164
    @2
    @6
    @131
    @164
    @2
    wph
    @2
    cr
    wcel
    @163
    @46
    adantr
    #
    rexrd
    @164
    @6
    wph
    @6
    cr
    wcel
    @163
    @48
    adantr
    #
    rexrd
    @164
    @89
    cU
    wph
    @9
    cr
    @89
    @162
    sselda
    #
    wph
    cU
    cr
    wcel
    @163
    @50
    adantr
    #
    resubcld
    #
    @164
    @2
    @131
    clt
    wbr
    @3
    @131
    cU
    caddc
    co
    #
    clt
    wbr
    @164
    @0
    @89
    @3
    @172
    clt
    @164
    @0
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @163
    @0
    @89
    clt
    wbr
    wph
    @173
    @163
    wph
    @0
    @45
    rexrd
    adantr
    #
    wph
    @174
    @163
    wph
    @5
    @47
    rexrd
    adantr
    #
    wph
    @163
    simpr
    #
    @0
    @5
    @89
    ioogtlb
    syl3anc
    wph
    @3
    @0
    wceq
    @163
    @157
    adantr
    @164
    @89
    cU
    @164
    @89
    @169
    recnd
    #
    @164
    cU
    @170
    recnd
    npcand
    #
    3brtr4d
    @164
    @2
    @131
    cU
    @167
    @171
    @170
    ltadd1d
    mpbird
    @164
    @131
    @6
    clt
    wbr
    @172
    @7
    clt
    wbr
    @164
    @89
    @5
    @172
    @7
    clt
    @164
    @173
    @174
    @163
    @89
    @5
    clt
    wbr
    @175
    @176
    @177
    @0
    @5
    @89
    iooltub
    syl3anc
    @179
    wph
    @7
    @5
    wceq
    @163
    @158
    adantr
    3brtr4d
    @164
    @131
    @6
    cU
    @171
    @168
    @170
    ltadd1d
    mpbird
    eliood
    @131
    @11
    cF
    fvres
    syl
    @164
    @166
    @89
    @6
    @5
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cF
    cfv
    @160
    @164
    @131
    @183
    cF
    @164
    @131
    @89
    @49
    cmin
    co
    #
    @89
    @180
    caddc
    co
    @183
    @131
    @184
    wceq
    @164
    cU
    @49
    @89
    cmin
    fourierdlem90.u
    oveq2i
    a1i
    @164
    @89
    @5
    @6
    @178
    wph
    @5
    cc
    wcel
    @163
    @150
    adantr
    #
    wph
    @6
    cc
    wcel
    @163
    @149
    adantr
    #
    subsub2d
    @164
    @180
    @182
    @89
    caddc
    @164
    @182
    @180
    @164
    @180
    cT
    @164
    @6
    @5
    @186
    @185
    subcld
    wph
    cT
    cc
    wcel
    @163
    wph
    cT
    wph
    cT
    @91
    cr
    fourierdlem90.t
    wph
    cB
    cA
    @18
    @17
    resubcld
    syl5eqel
    #
    recnd
    #
    adantr
    wph
    cT
    cc0
    wne
    @163
    wph
    cT
    wph
    cc0
    @91
    cT
    clt
    wph
    @15
    cc0
    @91
    clt
    wbr
    @20
    wph
    cA
    cB
    @17
    @18
    posdifd
    mpbid
    fourierdlem90.t
    syl6breqr
    gt0ne0d
    #
    adantr
    divcan1d
    eqcomd
    oveq2d
    3eqtrd
    fveq2d
    @164
    vx
    cT
    cF
    @181
    @89
    wph
    cr
    cc
    cF
    wf
    @163
    fourierdlem90.f
    adantr
    wph
    cT
    cr
    wcel
    @163
    @187
    adantr
    wph
    @181
    cz
    wcel
    @163
    wph
    @181
    cB
    @5
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
    @181
    @192
    cT
    cmul
    co
    #
    cT
    cdiv
    co
    @192
    wph
    @180
    @193
    cT
    cdiv
    wph
    @180
    @5
    @193
    caddc
    co
    #
    @5
    cmin
    co
    @193
    wph
    @6
    @194
    @5
    cmin
    wph
    vx
    @5
    @100
    cB
    @100
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
    @194
    cr
    cE
    cr
    cE
    vx
    cr
    @199
    cmpt
    wceq
    wph
    fourierdlem90.e
    a1i
    @100
    @5
    wceq
    #
    @199
    @194
    wceq
    wph
    @200
    @100
    @5
    @198
    @193
    caddc
    @200
    id
    @200
    @197
    @192
    cT
    cmul
    @200
    @196
    @191
    cfl
    @200
    @195
    @190
    cT
    cdiv
    @100
    @5
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    @47
    wph
    @5
    @193
    @47
    wph
    @192
    cT
    wph
    @192
    wph
    @191
    wph
    @190
    cT
    wph
    cB
    @5
    @18
    @47
    resubcld
    @187
    @189
    redivcld
    flcld
    #
    zred
    #
    @187
    remulcld
    readdcld
    fvmptd
    oveq1d
    wph
    @5
    @193
    @150
    wph
    @192
    cT
    wph
    @192
    @202
    recnd
    #
    @188
    mulcld
    pncan2d
    eqtrd
    oveq1d
    wph
    @192
    cT
    @203
    @188
    @189
    divcan4d
    eqtrd
    @201
    eqeltrd
    adantr
    @169
    wph
    @118
    @100
    cT
    caddc
    co
    cF
    cfv
    @100
    cF
    cfv
    wceq
    @163
    fourierdlem90.6
    adantlr
    fperiodmul
    eqtrd
    3eqtrrd
    mpteq2dva
    3eqtrrd
    3eqtrd
    wph
    @8
    @9
    cc
    ccncf
    @159
    oveq1d
    3eltr3d
end
