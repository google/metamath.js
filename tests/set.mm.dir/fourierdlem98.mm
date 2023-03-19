include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt.mm"
include "cioc.mm"
include "wceq.mm"
include "cif.mm"
include "c1.mm"
include "cioo.mm"
include "cres.mm"
include "cpr.mm"
include "crn.mm"
include "wcel.mm"
include "cz.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
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
include "eqcomd.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "syl5req.mm"
include "supeq1d.mm"
include "fourierdlem90.mm"

theorem fourierdlem98
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cJ: class J
  let cM: class M
  let cV: class V
  let vp: setvar p
  let vf: setvar f
  let vl: setvar l
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume fourierdlem98.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem98.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem98.t: |- T = ( B - A )
  assume fourierdlem98.m: |- ( ph -> M e. NN )
  assume fourierdlem98.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem98.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem98.qcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem98.c: |- ( ph -> C e. RR )
  assume fourierdlem98.d: |- ( ph -> D e. ( C (,) +oo ) )
  assume fourierdlem98.j: |- ( ph -> J e. ( 0 ..^ ( ( # ` ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } ) ) - 1 ) ) )
  assume fourierdlem98.v: |- V = ( iota g g Isom < , < ( ( 0 ... ( ( # ` ( { C , D } u. { y e. ( C [,] D ) | E. k e. ZZ ( y + ( k x. T ) ) e. ran Q } ) ) - 1 ) ) , ( { C , D } u. { y e. ( C [,] D ) | E. h e. ZZ ( y + ( h x. T ) ) e. ran Q } ) ) )

  disjoint A i
  disjoint A x
  disjoint i x
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B i
  disjoint B x
  disjoint B m
  disjoint B p
  disjoint C g
  disjoint C y
  disjoint g y
  disjoint C i
  disjoint C x
  disjoint i y
  disjoint x y
  disjoint C m
  disjoint C p
  disjoint m y
  disjoint p y
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
  disjoint Q x
  disjoint i k
  disjoint k x
  disjoint Q m
  disjoint Q p
  disjoint k m
  disjoint k p
  disjoint T g
  disjoint T k
  disjoint T y
  disjoint T h
  disjoint T i
  disjoint T x
  disjoint T m
  disjoint T p
  disjoint V i
  disjoint V x
  disjoint V p
  disjoint i ph
  disjoint ph x
  disjoint k x
  disjoint A f
  disjoint A l
  disjoint A t
  disjoint A u
  disjoint A w
  disjoint f l
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint l t
  disjoint l u
  disjoint l w
  disjoint t u
  disjoint t w
  disjoint u w
  disjoint i l
  disjoint i t
  disjoint i u
  disjoint i w
  disjoint l x
  disjoint t x
  disjoint u x
  disjoint w x
  disjoint A z
  disjoint f z
  disjoint l z
  disjoint u z
  disjoint B f
  disjoint B l
  disjoint B t
  disjoint B u
  disjoint B w
  disjoint B v
  disjoint f v
  disjoint l v
  disjoint t v
  disjoint v w
  disjoint B z
  disjoint C f
  disjoint C l
  disjoint f g
  disjoint f y
  disjoint g l
  disjoint l y
  disjoint C z
  disjoint i z
  disjoint x z
  disjoint y z
  disjoint D f
  disjoint D l
  disjoint D z
  disjoint F z
  disjoint J z
  disjoint M f
  disjoint M l
  disjoint M t
  disjoint M w
  disjoint Q f
  disjoint Q l
  disjoint f k
  disjoint k l
  disjoint h l
  disjoint Q z
  disjoint k z
  disjoint Q t
  disjoint Q w
  disjoint T f
  disjoint T l
  disjoint T z
  disjoint T t
  disjoint T v
  disjoint T w
  disjoint V f
  disjoint V l
  disjoint V z
  disjoint f ph
  disjoint l ph
  disjoint ph z
  disjoint i v
  disjoint v x
  disjoint v z
  assert |- ( ph -> ( F |` ( ( V ` J ) (,) ( V ` ( J + 1 ) ) ) ) e. ( ( ( V ` J ) (,) ( V ` ( J + 1 ) ) ) -cn-> CC ) )

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
    vz
    cJ
    cV
    cfv
    vv
    cr
    vv
    cv
    #
    cB
    @0
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
    @8
    cif
    #
    cmpt
    #
    cfv
    #
    cJ
    c1
    caddc
    co
    cV
    cfv
    #
    @13
    @6
    cfv
    #
    cmin
    co
    #
    caddc
    co
    @14
    @15
    caddc
    co
    cioo
    co
    vz
    cv
    #
    @15
    cmin
    co
    cF
    @12
    @14
    cioo
    co
    cres
    #
    cfv
    cmpt
    #
    cV
    cT
    @15
    vf
    vi
    vl
    vm
    @6
    cF
    @17
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
    vw
    cr
    vt
    cv
    #
    cQ
    cfv
    #
    vw
    cv
    #
    @6
    cfv
    #
    @11
    cfv
    #
    cle
    wbr
    #
    vt
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
    @11
    cM
    @19
    @20
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
    @24
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @27
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
    @48
    cfv
    cD
    wceq
    wa
    vi
    cv
    #
    @48
    cfv
    @50
    c1
    caddc
    co
    @48
    cfv
    clt
    wbr
    vi
    cc0
    @49
    cfzo
    co
    wral
    wa
    vp
    cr
    cc0
    @49
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    vp
    fourierdlem98.p
    fourierdlem98.t
    fourierdlem98.m
    fourierdlem98.q
    wph
    cr
    cr
    cc
    cF
    fourierdlem98.f
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    fourierdlem98.fper
    fourierdlem98.qcn
    fourierdlem98.c
    fourierdlem98.d
    @51
    eqid
    @19
    @16
    @22
    caddc
    co
    #
    @24
    wcel
    #
    vl
    cz
    wrex
    #
    vz
    @27
    crab
    #
    cun
    @29
    @55
    @28
    @19
    @54
    @26
    vz
    vy
    @27
    @16
    @20
    wceq
    #
    @53
    @25
    vl
    cz
    @56
    @52
    @23
    @24
    @16
    @20
    @22
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    eqcomi
    @46
    @29
    chash
    cfv
    c1
    cmin
    @45
    @29
    chash
    @44
    @28
    @19
    @43
    @26
    vy
    @27
    @43
    @26
    wb
    @20
    @27
    wcel
    #
    @42
    @25
    vk
    vl
    cz
    @39
    @21
    wceq
    #
    @41
    @23
    @24
    @58
    @40
    @22
    @20
    caddc
    @39
    @21
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
    @47
    cfz
    co
    #
    @29
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    cio
    @59
    @19
    @20
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
    @24
    wcel
    #
    vh
    cz
    wrex
    #
    vy
    @27
    crab
    #
    cun
    #
    clt
    clt
    @60
    wiso
    #
    vg
    cio
    @59
    @29
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
    @61
    @69
    vg
    @29
    @68
    wceq
    @61
    @69
    wb
    @28
    @67
    @19
    @26
    @66
    vy
    @27
    @26
    @66
    wb
    @57
    @25
    @65
    vl
    vh
    cz
    @21
    @62
    wceq
    #
    @23
    @64
    @24
    @72
    @22
    @63
    @20
    caddc
    @21
    @62
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    a1i
    rabbiia
    uneq2i
    @59
    @29
    @68
    clt
    clt
    @60
    isoeq5
    ax-mp
    iotabii
    @71
    @61
    vf
    vg
    @59
    @29
    clt
    clt
    @60
    @70
    isoeq1
    cbviotav
    fourierdlem98.v
    3eqtr4ri
    vv
    vx
    cr
    @5
    vx
    cv
    #
    cB
    @73
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
    @0
    @73
    wceq
    #
    @0
    @73
    @4
    @77
    caddc
    @78
    id
    @78
    @3
    @76
    cT
    cmul
    @78
    @2
    @75
    cfl
    @78
    @1
    @74
    cT
    cdiv
    @0
    @73
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
    @7
    @10
    @16
    cB
    wceq
    #
    cA
    @16
    cif
    @8
    @16
    wceq
    #
    @9
    @79
    @8
    @16
    cA
    @8
    @16
    cB
    eqeq1
    @80
    id
    ifbieq2d
    cbvmptv
    fourierdlem98.j
    @15
    eqid
    @17
    eqid
    @18
    eqid
    vw
    vx
    cr
    @38
    @50
    cQ
    cfv
    #
    @73
    @6
    cfv
    #
    @11
    cfv
    #
    cle
    wbr
    #
    vi
    @36
    crab
    #
    cr
    clt
    csup
    @32
    @73
    wceq
    #
    cr
    @37
    @85
    clt
    @86
    @85
    @31
    @83
    cle
    wbr
    #
    vt
    @36
    crab
    @37
    @84
    @87
    vi
    vt
    @36
    @50
    @30
    wceq
    @81
    @31
    @83
    cle
    @50
    @30
    cQ
    fveq2
    breq1d
    cbvrabv
    @86
    @87
    @35
    vt
    @36
    @86
    @83
    @34
    @31
    cle
    @86
    @34
    @83
    @86
    @33
    @82
    @11
    @32
    @73
    @6
    fveq2
    fveq2d
    eqcomd
    breq2d
    rabbidv
    syl5req
    supeq1d
    cbvmptv
    fourierdlem90
end
