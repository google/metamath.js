include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cpr.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "crn.mm"
include "wcel.mm"
include "cz.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "clt.mm"
include "wiso.mm"
include "cio.mm"
include "cr.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmpt.mm"
include "cioc.mm"
include "wceq.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "cfzo.mm"
include "csup.mm"
include "cn.mm"
include "wa.mm"
include "wral.mm"
include "cmap.mm"
include "eqid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "uneq2i.mm"
include "wb.mm"
include "oveq2d.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "rabbiia.mm"
include "fveq2i.mm"
include "oveq1i.mm"
include "isoeq5.mm"
include "ax-mp.mm"
include "isoeq1.mm"
include "syl5bb.mm"
include "cbviotav.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "fourierdlem109.mm"

theorem fourierdlem110
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cL: class L
  let cM: class M
  let cX: class X
  let vp: setvar p
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vl: setvar l
  assume fourierdlem110.a: |- ( ph -> A e. RR )
  assume fourierdlem110.b: |- ( ph -> B e. RR )
  assume fourierdlem110.t: |- T = ( B - A )
  assume fourierdlem110.x: |- ( ph -> X e. RR )
  assume fourierdlem110.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem110.m: |- ( ph -> M e. NN )
  assume fourierdlem110.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem110.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem110.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem110.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem110.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem110.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )

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
  disjoint F i
  disjoint F x
  disjoint L x
  disjoint M i
  disjoint M x
  disjoint M m
  disjoint M p
  disjoint Q i
  disjoint Q x
  disjoint Q m
  disjoint Q p
  disjoint R x
  disjoint T i
  disjoint T x
  disjoint T m
  disjoint T p
  disjoint X i
  disjoint X x
  disjoint X m
  disjoint X p
  disjoint i ph
  disjoint ph x
  disjoint A f
  disjoint A g
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint A y
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f y
  disjoint g j
  disjoint g k
  disjoint g w
  disjoint g y
  disjoint j k
  disjoint j w
  disjoint j y
  disjoint k w
  disjoint k y
  disjoint w y
  disjoint g i
  disjoint g x
  disjoint i j
  disjoint i k
  disjoint i w
  disjoint i y
  disjoint j x
  disjoint k x
  disjoint w x
  disjoint x y
  disjoint g m
  disjoint g p
  disjoint j m
  disjoint j p
  disjoint m y
  disjoint p y
  disjoint A z
  disjoint f z
  disjoint j z
  disjoint k z
  disjoint w z
  disjoint y z
  disjoint B f
  disjoint B g
  disjoint B j
  disjoint B k
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F j
  disjoint F w
  disjoint L w
  disjoint M f
  disjoint M j
  disjoint M k
  disjoint M w
  disjoint M z
  disjoint i z
  disjoint x z
  disjoint Q f
  disjoint Q g
  disjoint Q j
  disjoint Q k
  disjoint Q l
  disjoint Q w
  disjoint Q y
  disjoint f l
  disjoint g l
  disjoint j l
  disjoint k l
  disjoint l w
  disjoint l y
  disjoint i l
  disjoint l x
  disjoint l m
  disjoint l p
  disjoint Q z
  disjoint R w
  disjoint T f
  disjoint T g
  disjoint T j
  disjoint T k
  disjoint T l
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint X f
  disjoint X g
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X y
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint ph w
  disjoint k x
  assert |- ( ph -> S. ( ( A - X ) [,] ( B - X ) ) ( F ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
    vx
    vw
    cA
    cB
    cP
    cQ
    cR
    cc0
    cA
    cX
    cmin
    co
    #
    cB
    cX
    cmin
    co
    #
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
    @0
    @1
    cicc
    co
    #
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
    cfz
    co
    #
    @12
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    cio
    cT
    vf
    vi
    vj
    vk
    vm
    vy
    cr
    @3
    cB
    @3
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
    cF
    @2
    @3
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
    @7
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @10
    crab
    #
    cun
    #
    vz
    cr
    vj
    cv
    cQ
    cfv
    #
    vz
    cv
    #
    @23
    cfv
    #
    vy
    cA
    cB
    cioc
    co
    #
    @3
    cB
    wceq
    #
    cA
    @3
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
    @37
    cL
    cM
    @14
    vm
    cn
    cc0
    vp
    cv
    #
    cfv
    @0
    wceq
    vm
    cv
    #
    @43
    cfv
    @1
    wceq
    wa
    vi
    cv
    #
    @43
    cfv
    @45
    c1
    caddc
    co
    @43
    cfv
    clt
    wbr
    vi
    cc0
    @44
    cfzo
    co
    wral
    wa
    vp
    cr
    cc0
    @44
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    cX
    vp
    fourierdlem110.a
    fourierdlem110.b
    fourierdlem110.t
    fourierdlem110.x
    fourierdlem110.p
    fourierdlem110.m
    fourierdlem110.q
    fourierdlem110.f
    fourierdlem110.fper
    fourierdlem110.fcn
    fourierdlem110.r
    fourierdlem110.l
    @46
    eqid
    @29
    vx
    cv
    #
    @25
    caddc
    co
    #
    @7
    wcel
    #
    vk
    cz
    wrex
    #
    vx
    @10
    crab
    @2
    @28
    @50
    vy
    vx
    @10
    @3
    @47
    wceq
    #
    @27
    @49
    vk
    cz
    @51
    @26
    @48
    @7
    @3
    @47
    @25
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    @13
    @30
    chash
    cfv
    c1
    cmin
    @12
    @30
    chash
    @11
    @29
    @2
    @9
    @28
    vy
    @10
    @9
    @28
    wb
    @3
    @10
    wcel
    @8
    @27
    vl
    vk
    cz
    @4
    @24
    wceq
    #
    @6
    @26
    @7
    @52
    @5
    @25
    @3
    caddc
    @4
    @24
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    a1i
    rabbiia
    uneq2i
    #
    fveq2i
    oveq1i
    @17
    @15
    @30
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vg
    vf
    @17
    @15
    @30
    clt
    clt
    @16
    wiso
    #
    @16
    @54
    wceq
    @55
    @12
    @30
    wceq
    @17
    @56
    wb
    @53
    @15
    @12
    @30
    clt
    clt
    @16
    isoeq5
    ax-mp
    @15
    @30
    clt
    clt
    @54
    @16
    isoeq1
    syl5bb
    cbviotav
    vy
    vx
    cr
    @22
    @47
    cB
    @47
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
    @51
    @3
    @47
    @21
    @60
    caddc
    @51
    id
    @51
    @20
    @59
    cT
    cmul
    @51
    @19
    @58
    cfl
    @51
    @18
    @57
    cT
    cdiv
    @3
    @47
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    vy
    vw
    @34
    @36
    vw
    cv
    #
    cB
    wceq
    #
    cA
    @61
    cif
    @3
    @61
    wceq
    #
    @35
    @62
    @3
    @61
    cA
    @3
    @61
    cB
    eqeq1
    @63
    id
    ifbieq2d
    cbvmptv
    vz
    vx
    cr
    @42
    @31
    @47
    @23
    cfv
    #
    @37
    cfv
    #
    cle
    wbr
    #
    vj
    @40
    crab
    #
    cr
    clt
    csup
    @32
    @47
    wceq
    #
    cr
    @41
    @67
    clt
    @68
    @39
    @66
    vj
    @40
    @68
    @38
    @65
    @31
    cle
    @68
    @33
    @64
    @37
    @32
    @47
    @23
    fveq2
    fveq2d
    breq2d
    rabbidv
    supeq1d
    cbvmptv
    fourierdlem109
end
