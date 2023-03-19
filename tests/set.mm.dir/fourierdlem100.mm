include "cicc.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cibl.mm"
include "cr.mm"
include "cc.mm"
include "cpnf.mm"
include "cioo.mm"
include "wcel.mm"
include "elioore.mm"
include "syl.mm"
include "iccssred.mm"
include "feqresmpt.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "cif.mm"
include "c1.mm"
include "caddc.mm"
include "cn.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "wb.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "a1i.mm"
include "rabbiia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "cpr.mm"
include "cmin.mm"
include "cmul.mm"
include "crn.mm"
include "cz.mm"
include "wrex.mm"
include "cun.mm"
include "wiso.mm"
include "cxr.mm"
include "w3a.mm"
include "elioo4g.mm"
include "sylib.mm"
include "simprd.mm"
include "simpld.mm"
include "id.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "uneq2i.mm"
include "chash.mm"
include "eleq1i.mm"
include "rexbii.mm"
include "rgenw.mm"
include "rabbi.mm"
include "mpbi.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "cio.mm"
include "isoeq5.mm"
include "ax-mp.mm"
include "iotabii.mm"
include "fourierdlem54.mm"
include "fssresd.mm"
include "ccncf.mm"
include "ioossicc.mm"
include "adantr.mm"
include "rexrd.mm"
include "wf.mm"
include "fourierdlem15.mm"
include "simpr.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "resabs1d.mm"
include "adantlr.mm"
include "eqid.mm"
include "fourierdlem90.mm"
include "eqeltrd.mm"
include "climc.mm"
include "fourierdlem89.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "fourierdlem91.mm"
include "fourierdlem69.mm"
include "eqeltrrd.mm"

theorem fourierdlem100
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
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vj: setvar j
  assume fourierlemiblglemlem.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem100.t: |- T = ( B - A )
  assume fourierdlem100.m: |- ( ph -> M e. NN )
  assume fourierdlem100.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem100.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem100.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem100.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem100.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem100.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem100.c: |- ( ph -> C e. RR )
  assume fourierdlem100.d: |- ( ph -> D e. ( C (,) +oo ) )
  assume fourierdlem100.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = C /\ ( p ` m ) = D ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem100.n: |- N = ( ( # ` H ) - 1 )
  assume fourierdlem100.h: |- H = ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } )
  assume fourierdlem100.s: |- S = ( iota f f Isom < , < ( ( 0 ... N ) , H ) )
  assume fourierdlem100.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem100.j: |- J = ( y e. ( A (,] B ) |-> if ( y = B , A , y ) )
  assume fourierdlem100.i: |- I = ( x e. RR |-> sup ( { i e. ( 0 ..^ M ) | ( Q ` i ) <_ ( J ` ( E ` x ) ) } , RR , < ) )

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
  disjoint H f
  disjoint H y
  disjoint H x
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint I i
  disjoint I x
  disjoint J i
  disjoint J x
  disjoint J y
  disjoint L x
  disjoint L y
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint M x
  disjoint M y
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
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S k
  disjoint S y
  disjoint S i
  disjoint S x
  disjoint S p
  disjoint T f
  disjoint T k
  disjoint T y
  disjoint T i
  disjoint T x
  disjoint f ph
  disjoint k ph
  disjoint ph y
  disjoint i ph
  disjoint ph x
  disjoint k x
  disjoint C j
  disjoint f j
  disjoint j y
  disjoint i j
  disjoint j m
  disjoint j p
  disjoint j x
  disjoint D j
  disjoint F j
  disjoint N j
  disjoint j k
  disjoint S j
  disjoint j ph
  assert |- ( ph -> ( x e. ( C [,] D ) |-> ( F ` x ) ) e. L^1 )

  proof
    wph
    cF
    cC
    cD
    cicc
    co
    #
    cres
    #
    vx
    @0
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    cibl
    wph
    vx
    cr
    cc
    @0
    cF
    fourierdlem100.f
    wph
    cC
    cD
    fourierdlem100.c
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
    fourierdlem100.d
    cD
    cC
    cpnf
    elioore
    #
    syl
    #
    iccssred
    #
    feqresmpt
    wph
    cC
    cD
    cO
    cS
    vj
    cv
    #
    cS
    cfv
    #
    cE
    cfv
    cJ
    cfv
    #
    @10
    cI
    cfv
    #
    cQ
    cfv
    wceq
    @12
    vi
    cc0
    cM
    cfzo
    co
    #
    cR
    cmpt
    #
    cfv
    @11
    cF
    cfv
    cif
    #
    vj
    vm
    @1
    @9
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
    @12
    c1
    caddc
    co
    cQ
    cfv
    wceq
    @12
    vi
    @13
    cL
    cmpt
    #
    cfv
    @18
    cF
    cfv
    cif
    #
    cN
    vp
    cO
    vm
    cn
    cc0
    vp
    cv
    #
    cfv
    cC
    wceq
    vm
    cv
    #
    @21
    cfv
    cD
    wceq
    wa
    #
    vi
    cv
    #
    @21
    cfv
    #
    @24
    c1
    caddc
    co
    #
    @21
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    @22
    cfzo
    co
    #
    wral
    #
    wa
    #
    vp
    cr
    cc0
    @22
    cfz
    co
    cmap
    co
    #
    crab
    #
    cmpt
    vm
    cn
    @23
    @9
    @21
    cfv
    #
    @16
    @21
    cfv
    #
    clt
    wbr
    #
    vj
    @29
    wral
    #
    wa
    #
    vp
    @32
    crab
    #
    cmpt
    fourierdlem100.o
    vm
    cn
    @33
    @39
    @31
    @38
    vp
    @32
    @31
    @38
    wb
    @21
    @32
    wcel
    @30
    @37
    @23
    @28
    @36
    vi
    vj
    @29
    @24
    @9
    wceq
    #
    @25
    @34
    @27
    @35
    clt
    @24
    @9
    @21
    fveq2
    @40
    @26
    @16
    @21
    @24
    @9
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    cbvralv
    anbi2i
    a1i
    rabbiia
    mpteq2i
    eqtri
    wph
    cN
    cn
    wcel
    #
    cS
    cN
    cO
    cfv
    wcel
    #
    wph
    @41
    @42
    wa
    cc0
    cN
    cfz
    co
    #
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
    @0
    crab
    #
    cun
    #
    clt
    clt
    cS
    wiso
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
    @54
    cM
    cN
    cO
    vp
    fourierdlem100.t
    fourierlemiblglemlem.p
    fourierdlem100.m
    fourierdlem100.q
    fourierdlem100.c
    @7
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
    @5
    w3a
    #
    @55
    @56
    wa
    #
    wph
    @4
    @57
    @58
    wa
    fourierdlem100.d
    cC
    cpnf
    cD
    elioo4g
    sylib
    simprd
    simpld
    fourierdlem100.o
    @53
    @2
    @46
    cT
    cmul
    co
    #
    caddc
    co
    #
    @50
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    @0
    crab
    @44
    @52
    @62
    vy
    vx
    @0
    @45
    @2
    wceq
    #
    @51
    @61
    vk
    cz
    @63
    @49
    @60
    @50
    @63
    @45
    @2
    @48
    @59
    caddc
    @63
    id
    @48
    @59
    wceq
    @63
    @47
    cT
    @46
    cmul
    cT
    @47
    fourierdlem100.t
    eqcomi
    oveq2i
    #
    a1i
    oveq12d
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    cN
    cH
    chash
    cfv
    #
    c1
    cmin
    co
    @54
    chash
    cfv
    #
    c1
    cmin
    co
    fourierdlem100.n
    @65
    @66
    c1
    cmin
    cH
    @54
    chash
    cH
    @44
    @45
    @59
    caddc
    co
    #
    @50
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @0
    crab
    #
    cun
    @54
    fourierdlem100.h
    @70
    @53
    @44
    @69
    @52
    wb
    #
    vy
    @0
    wral
    @70
    @53
    wceq
    @71
    vy
    @0
    @68
    @51
    vk
    cz
    @67
    @49
    @50
    @59
    @48
    @45
    caddc
    @48
    @59
    @64
    eqcomi
    oveq2i
    eleq1i
    rexbii
    rgenw
    @69
    @52
    vy
    @0
    rabbi
    mpbi
    uneq2i
    eqtri
    #
    fveq2i
    oveq1i
    eqtri
    cS
    @43
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
    @43
    @54
    clt
    clt
    @73
    wiso
    #
    vf
    cio
    fourierdlem100.s
    @74
    @75
    vf
    cH
    @54
    wceq
    @74
    @75
    wb
    @72
    @43
    cH
    @54
    clt
    clt
    @73
    isoeq5
    ax-mp
    iotabii
    eqtri
    fourierdlem54
    simpld
    #
    simpld
    #
    wph
    @41
    @42
    @76
    simprd
    #
    wph
    cr
    cc
    @0
    cF
    fourierdlem100.f
    @8
    fssresd
    wph
    @9
    cc0
    cN
    cfzo
    co
    wcel
    #
    wa
    #
    @1
    @10
    @17
    cioo
    co
    #
    cres
    #
    cF
    @81
    cres
    #
    @81
    cc
    ccncf
    co
    @80
    cF
    @81
    @0
    @80
    @81
    @10
    @17
    cicc
    co
    @0
    @10
    @17
    ioossicc
    @80
    cC
    cD
    cS
    @9
    cN
    @80
    cC
    wph
    cC
    cr
    wcel
    @79
    fourierdlem100.c
    adantr
    #
    rexrd
    @80
    cD
    @80
    @4
    @5
    wph
    @4
    @79
    fourierdlem100.d
    adantr
    #
    @6
    syl
    rexrd
    wph
    @43
    @0
    cS
    wf
    @79
    wph
    cC
    cD
    cO
    cS
    vi
    vm
    cN
    vp
    fourierdlem100.o
    @77
    @78
    fourierdlem15
    adantr
    wph
    @79
    simpr
    #
    fourierdlem8
    syl5ss
    resabs1d
    #
    @80
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cQ
    vy
    @11
    @17
    @18
    cmin
    co
    #
    caddc
    co
    @18
    @88
    caddc
    co
    cioo
    co
    @45
    @88
    cmin
    co
    cF
    @11
    @18
    cioo
    co
    cres
    #
    cfv
    cmpt
    #
    cS
    cT
    @88
    vf
    vi
    vk
    vm
    cE
    cF
    @89
    cH
    cI
    @9
    cJ
    cM
    cN
    cO
    vp
    fourierlemiblglemlem.p
    fourierdlem100.t
    wph
    cM
    cn
    wcel
    @79
    fourierdlem100.m
    adantr
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    @79
    fourierdlem100.q
    adantr
    #
    wph
    cr
    cc
    cF
    wf
    @79
    fourierdlem100.f
    adantr
    #
    wph
    @2
    cr
    wcel
    @2
    cT
    caddc
    co
    cF
    cfv
    @3
    wceq
    @79
    fourierdlem100.per
    adantlr
    #
    wph
    @24
    @13
    wcel
    #
    cF
    @24
    cQ
    cfv
    #
    @26
    cQ
    cfv
    #
    cioo
    co
    #
    cres
    #
    @98
    cc
    ccncf
    co
    wcel
    @79
    fourierdlem100.fcn
    adantlr
    #
    @84
    @85
    fourierdlem100.o
    fourierdlem100.h
    fourierdlem100.n
    fourierdlem100.s
    fourierdlem100.e
    fourierdlem100.j
    @86
    @88
    eqid
    #
    @89
    eqid
    @90
    eqid
    fourierdlem100.i
    fourierdlem90
    eqeltrd
    @80
    @15
    @83
    @10
    climc
    co
    @82
    @10
    climc
    co
    @80
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    @88
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @9
    cM
    cN
    cO
    @14
    cJ
    vp
    fourierlemiblglemlem.p
    fourierdlem100.t
    @91
    @92
    @93
    @94
    @100
    wph
    @95
    cR
    @99
    @96
    climc
    co
    wcel
    @79
    fourierdlem100.r
    adantlr
    @84
    @85
    fourierdlem100.o
    fourierdlem100.h
    fourierdlem100.n
    fourierdlem100.s
    fourierdlem100.e
    fourierdlem100.j
    @86
    @101
    fourierdlem100.i
    @14
    eqid
    fourierdlem89
    @80
    @83
    @82
    @10
    climc
    @80
    @82
    @83
    @87
    eqcomd
    #
    oveq1d
    eleqtrd
    @80
    @20
    @83
    @17
    climc
    co
    @82
    @17
    climc
    co
    @80
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
    @88
    vf
    vi
    vk
    vm
    cE
    cF
    cH
    cI
    @9
    cL
    cM
    cN
    cO
    @19
    cJ
    vp
    fourierlemiblglemlem.p
    fourierdlem100.t
    @91
    @92
    @93
    @94
    @100
    wph
    @95
    cL
    @99
    @97
    climc
    co
    wcel
    @79
    fourierdlem100.l
    adantlr
    @84
    @85
    fourierdlem100.o
    fourierdlem100.h
    fourierdlem100.n
    fourierdlem100.s
    fourierdlem100.e
    fourierdlem100.j
    @86
    @101
    fourierdlem100.i
    @19
    eqid
    fourierdlem91
    @80
    @83
    @82
    @17
    climc
    @102
    oveq1d
    eleqtrd
    fourierdlem69
    eqeltrrd
end
