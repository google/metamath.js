include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "cmpt.mm"
include "cpr.mm"
include "crn.mm"
include "wcel.mm"
include "cz.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
include "cioc.mm"
include "wceq.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "clt.mm"
include "csup.mm"
include "chash.mm"
include "cn.mm"
include "wa.mm"
include "wral.mm"
include "cfz.mm"
include "cmap.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "eqid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "uneq2i.mm"
include "eqcomi.mm"
include "wb.mm"
include "oveq2d.mm"
include "cbvrexv.mm"
include "rabbiia.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "wiso.mm"
include "cio.mm"
include "isoeq5.mm"
include "ax-mp.mm"
include "iotabii.mm"
include "isoeq1.mm"
include "cbviotav.mm"
include "3eqtr4ri.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "supeq1d.mm"
include "fourierdlem91.mm"

theorem fourierdlem99
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cJ: class J
  let cL: class L
  let cM: class M
  let cV: class V
  let vp: setvar p
  let vf: setvar f
  let vl: setvar l
  let vz: setvar z
  assume fourierdlem99.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem99.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem99.t: |- T = ( B - A )
  assume fourierdlem99.m: |- ( ph -> M e. NN )
  assume fourierdlem99.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem99.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem99.qcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem99.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem99.c: |- ( ph -> C e. RR )
  assume fourierdlem99.d: |- ( ph -> D e. ( C (,) +oo ) )
  assume fourierdlem99.j: |- ( ph -> J e. ( 0 ..^ ( ( # ` ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } ) ) - 1 ) ) )
  assume fourierdlem99.v: |- V = ( iota g g Isom < , < ( ( 0 ... ( ( # ` ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } ) ) - 1 ) ) , ( { C , D } u. { y e. ( C [,] D ) | E. h e. ZZ ( y + ( h x. T ) ) e. ran Q } ) ) )

  disjoint A j
  disjoint A u
  disjoint A y
  disjoint j u
  disjoint j y
  disjoint u y
  disjoint A i
  disjoint A x
  disjoint i j
  disjoint i u
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint u x
  disjoint x y
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint m y
  disjoint p y
  disjoint B j
  disjoint B u
  disjoint B y
  disjoint B i
  disjoint B x
  disjoint B m
  disjoint B p
  disjoint B v
  disjoint j v
  disjoint v y
  disjoint C g
  disjoint C y
  disjoint g y
  disjoint C i
  disjoint C x
  disjoint C m
  disjoint C p
  disjoint D g
  disjoint D y
  disjoint D i
  disjoint D x
  disjoint D m
  disjoint D p
  disjoint F i
  disjoint F x
  disjoint J i
  disjoint J x
  disjoint L x
  disjoint M j
  disjoint M y
  disjoint M i
  disjoint M x
  disjoint M m
  disjoint M p
  disjoint Q g
  disjoint Q k
  disjoint Q y
  disjoint g k
  disjoint k y
  disjoint Q h
  disjoint h y
  disjoint Q i
  disjoint Q j
  disjoint Q x
  disjoint Q m
  disjoint Q p
  disjoint i k
  disjoint k m
  disjoint k p
  disjoint T g
  disjoint T k
  disjoint T y
  disjoint T h
  disjoint T i
  disjoint T j
  disjoint T v
  disjoint T x
  disjoint i v
  disjoint v x
  disjoint T m
  disjoint T p
  disjoint V i
  disjoint V x
  disjoint V p
  disjoint i ph
  disjoint ph x
  disjoint k x
  disjoint k x
  disjoint A f
  disjoint A l
  disjoint A z
  disjoint f j
  disjoint f l
  disjoint f u
  disjoint f y
  disjoint f z
  disjoint j l
  disjoint j z
  disjoint l u
  disjoint l y
  disjoint l z
  disjoint u z
  disjoint y z
  disjoint i l
  disjoint i z
  disjoint l x
  disjoint x z
  disjoint B f
  disjoint B l
  disjoint B z
  disjoint f v
  disjoint l v
  disjoint v z
  disjoint C f
  disjoint C l
  disjoint f g
  disjoint g l
  disjoint C z
  disjoint D f
  disjoint D l
  disjoint D z
  disjoint F z
  disjoint J z
  disjoint L z
  disjoint M f
  disjoint M l
  disjoint M z
  disjoint Q f
  disjoint Q l
  disjoint f k
  disjoint k l
  disjoint h l
  disjoint Q z
  disjoint T f
  disjoint T l
  disjoint T z
  disjoint V f
  disjoint V l
  disjoint V z
  disjoint f ph
  disjoint l ph
  disjoint ph z
  disjoint k z
  assert |- ( ph -> if ( ( ( v e. RR |-> ( v + ( ( |_ ` ( ( B - v ) / T ) ) x. T ) ) ) ` ( V ` ( J + 1 ) ) ) = ( Q ` ( ( ( y e. RR |-> sup ( { j e. ( 0 ..^ M ) | ( Q ` j ) <_ ( ( u e. ( A (,] B ) |-> if ( u = B , A , u ) ) ` ( ( v e. RR |-> ( v + ( ( |_ ` ( ( B - v ) / T ) ) x. T ) ) ) ` y ) ) } , RR , < ) ) ` ( V ` J ) ) + 1 ) ) , ( ( i e. ( 0 ..^ M ) |-> L ) ` ( ( y e. RR |-> sup ( { j e. ( 0 ..^ M ) | ( Q ` j ) <_ ( ( u e. ( A (,] B ) |-> if ( u = B , A , u ) ) ` ( ( v e. RR |-> ( v + ( ( |_ ` ( ( B - v ) / T ) ) x. T ) ) ) ` y ) ) } , RR , < ) ) ` ( V ` J ) ) ) , ( F ` ( ( v e. RR |-> ( v + ( ( |_ ` ( ( B - v ) / T ) ) x. T ) ) ) ` ( V ` ( J + 1 ) ) ) ) ) e. ( ( F |` ( ( V ` J ) (,) ( V ` ( J + 1 ) ) ) ) limCC ( V ` ( J + 1 ) ) ) )

  proof
    wph
    vx
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cV
    cT
    cJ
    c1
    caddc
    co
    cV
    cfv
    #
    @0
    vv
    cr
    vv
    cv
    #
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
    cmpt
    #
    cfv
    cmin
    co
    #
    vf
    vi
    vl
    vm
    @7
    cF
    cC
    cD
    cpr
    #
    vy
    cv
    #
    vl
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
    vl
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
    vy
    cr
    vj
    cv
    #
    cQ
    cfv
    #
    @10
    @7
    cfv
    #
    vu
    cA
    cB
    cioc
    co
    #
    vu
    cv
    #
    cB
    wceq
    #
    cA
    @24
    cif
    #
    cmpt
    #
    cfv
    #
    cle
    wbr
    #
    vj
    cc0
    cM
    cfzo
    co
    #
    crab
    #
    cr
    clt
    csup
    #
    cmpt
    cJ
    cL
    cM
    @9
    @10
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
    @14
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @17
    crab
    #
    cun
    #
    chash
    cfv
    #
    c1
    cmin
    co
    #
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
    @42
    cfv
    cD
    wceq
    wa
    vi
    cv
    #
    @42
    cfv
    @44
    c1
    caddc
    co
    @42
    cfv
    clt
    wbr
    vi
    cc0
    @43
    cfzo
    co
    wral
    wa
    vp
    cr
    cc0
    @43
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    vi
    @30
    cL
    cmpt
    #
    @27
    vp
    fourierdlem99.p
    fourierdlem99.t
    fourierdlem99.m
    fourierdlem99.q
    wph
    cr
    cr
    cc
    cF
    fourierdlem99.f
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    fourierdlem99.fper
    fourierdlem99.qcn
    fourierdlem99.l
    fourierdlem99.c
    fourierdlem99.d
    @45
    eqid
    @9
    vz
    cv
    #
    @12
    caddc
    co
    #
    @14
    wcel
    #
    vl
    cz
    wrex
    #
    vz
    @17
    crab
    #
    cun
    @19
    @51
    @18
    @9
    @50
    @16
    vz
    vy
    @17
    @47
    @10
    wceq
    #
    @49
    @15
    vl
    cz
    @52
    @48
    @13
    @14
    @47
    @10
    @12
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    eqcomi
    @40
    @19
    chash
    cfv
    c1
    cmin
    @39
    @19
    chash
    @38
    @18
    @9
    @37
    @16
    vy
    @17
    @37
    @16
    wb
    @10
    @17
    wcel
    #
    @36
    @15
    vk
    vl
    cz
    @33
    @11
    wceq
    #
    @35
    @13
    @14
    @54
    @34
    @12
    @10
    caddc
    @33
    @11
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    a1i
    rabbiia
    uneq2i
    fveq2i
    oveq1i
    cc0
    @41
    cfz
    co
    #
    @19
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    cio
    @55
    @9
    @10
    vh
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @14
    wcel
    #
    vh
    cz
    wrex
    #
    vy
    @17
    crab
    #
    cun
    #
    clt
    clt
    @56
    wiso
    #
    vg
    cio
    @55
    @19
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vf
    cio
    cV
    @57
    @65
    vg
    @19
    @64
    wceq
    @57
    @65
    wb
    @18
    @63
    @9
    @16
    @62
    vy
    @17
    @16
    @62
    wb
    @53
    @15
    @61
    vl
    vh
    cz
    @11
    @58
    wceq
    #
    @13
    @60
    @14
    @68
    @12
    @59
    @10
    caddc
    @11
    @58
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    a1i
    rabbiia
    uneq2i
    @55
    @19
    @64
    clt
    clt
    @56
    isoeq5
    ax-mp
    iotabii
    @67
    @57
    vf
    vg
    @55
    @19
    clt
    clt
    @56
    @66
    isoeq1
    cbviotav
    fourierdlem99.v
    3eqtr4ri
    vv
    vx
    cr
    @6
    vx
    cv
    #
    cB
    @69
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
    @1
    @69
    wceq
    #
    @1
    @69
    @5
    @73
    caddc
    @74
    id
    @74
    @4
    @72
    cT
    cmul
    @74
    @3
    @71
    cfl
    @74
    @2
    @70
    cT
    cdiv
    @1
    @69
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    vu
    vz
    @23
    @26
    @47
    cB
    wceq
    #
    cA
    @47
    cif
    @24
    @47
    wceq
    #
    @25
    @75
    @24
    @47
    cA
    @24
    @47
    cB
    eqeq1
    @76
    id
    ifbieq2d
    cbvmptv
    fourierdlem99.j
    @8
    eqid
    vy
    vx
    cr
    @32
    @44
    cQ
    cfv
    #
    @69
    @7
    cfv
    #
    @27
    cfv
    #
    cle
    wbr
    #
    vi
    @30
    crab
    #
    cr
    clt
    csup
    @10
    @69
    wceq
    #
    cr
    @31
    @81
    clt
    @82
    @31
    @77
    @28
    cle
    wbr
    #
    vi
    @30
    crab
    @81
    @29
    @83
    vj
    vi
    @30
    @20
    @44
    wceq
    @21
    @77
    @28
    cle
    @20
    @44
    cQ
    fveq2
    breq1d
    cbvrabv
    @82
    @83
    @80
    vi
    @30
    @82
    @28
    @79
    @77
    cle
    @82
    @22
    @78
    @27
    @10
    @69
    @7
    fveq2
    fveq2d
    breq2d
    rabbidv
    syl5eq
    supeq1d
    cbvmptv
    @46
    eqid
    fourierdlem91
end
