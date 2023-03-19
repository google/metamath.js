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
include "rgenw.mm"
include "rabbi.mm"
include "mpbi.mm"
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
include "breq1d.mm"
include "syl6eq.mm"
include "supeq1d.mm"
include "fourierdlem107.mm"

theorem fourierdlem108
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
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vj: setvar j
  let vz: setvar z
  let vl: setvar l
  assume fourierdlem108.a: |- ( ph -> A e. RR )
  assume fourierdlem108.b: |- ( ph -> B e. RR )
  assume fourierdlem108.t: |- T = ( B - A )
  assume fourierdlem108.x: |- ( ph -> X e. RR+ )
  assume fourierdlem108.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem108.m: |- ( ph -> M e. NN )
  assume fourierdlem108.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem108.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem108.fper: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem108.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem108.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem108.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )

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
  disjoint A k
  disjoint A w
  disjoint A y
  disjoint f g
  disjoint f k
  disjoint f w
  disjoint f y
  disjoint g k
  disjoint g w
  disjoint g y
  disjoint k w
  disjoint k y
  disjoint w y
  disjoint g i
  disjoint g x
  disjoint i k
  disjoint i w
  disjoint i y
  disjoint k x
  disjoint w x
  disjoint x y
  disjoint A j
  disjoint A z
  disjoint f j
  disjoint f z
  disjoint j k
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k z
  disjoint w z
  disjoint y z
  disjoint i j
  disjoint j m
  disjoint j p
  disjoint m w
  disjoint p w
  disjoint B f
  disjoint B j
  disjoint B k
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint i z
  disjoint j x
  disjoint x z
  disjoint F j
  disjoint F y
  disjoint L y
  disjoint M f
  disjoint M j
  disjoint M k
  disjoint M y
  disjoint M z
  disjoint Q f
  disjoint Q g
  disjoint Q k
  disjoint Q l
  disjoint Q w
  disjoint Q y
  disjoint f l
  disjoint g l
  disjoint k l
  disjoint l w
  disjoint l y
  disjoint Q j
  disjoint Q z
  disjoint R y
  disjoint T f
  disjoint T g
  disjoint T k
  disjoint T l
  disjoint T w
  disjoint T y
  disjoint i l
  disjoint l x
  disjoint T j
  disjoint T z
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X w
  disjoint X y
  disjoint X j
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint g p
  disjoint l p
  disjoint l m
  disjoint k x
  assert |- ( ph -> S. ( ( A - X ) [,] ( B - X ) ) ( F ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
    vx
    vy
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
    cA
    cpr
    #
    vw
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
    vw
    @0
    cA
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
    @11
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
    vk
    vm
    vw
    cr
    @2
    cB
    @2
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
    @1
    @2
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
    @6
    wcel
    #
    vk
    cz
    wrex
    #
    vw
    @9
    crab
    #
    cun
    #
    vz
    cr
    vj
    cv
    #
    cQ
    cfv
    #
    vz
    cv
    #
    @22
    cfv
    #
    vw
    cA
    cB
    cioc
    co
    #
    @2
    cB
    wceq
    #
    cA
    @2
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
    cL
    cM
    @13
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
    cA
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
    @37
    vp
    fourierdlem108.a
    fourierdlem108.b
    fourierdlem108.t
    fourierdlem108.x
    fourierdlem108.p
    fourierdlem108.m
    fourierdlem108.q
    fourierdlem108.f
    fourierdlem108.fper
    fourierdlem108.fcn
    fourierdlem108.r
    fourierdlem108.l
    @46
    eqid
    @28
    vy
    cv
    #
    @24
    caddc
    co
    #
    @6
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @9
    crab
    @1
    @27
    @50
    vw
    vy
    @9
    @2
    @47
    wceq
    #
    @26
    @49
    vk
    cz
    @51
    @25
    @48
    @6
    @2
    @47
    @24
    caddc
    oveq1
    eleq1d
    rexbidv
    cbvrabv
    uneq2i
    @12
    @29
    chash
    cfv
    c1
    cmin
    @11
    @29
    chash
    @10
    @28
    @1
    @8
    @27
    wb
    #
    vw
    @9
    wral
    @10
    @28
    wceq
    @52
    vw
    @9
    @7
    @26
    vl
    vk
    cz
    @3
    @23
    wceq
    #
    @5
    @25
    @6
    @53
    @4
    @24
    @2
    caddc
    @3
    @23
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    rgenw
    @8
    @27
    vw
    @9
    rabbi
    mpbi
    uneq2i
    #
    fveq2i
    oveq1i
    @16
    @14
    @29
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vg
    vf
    @16
    @14
    @29
    clt
    clt
    @15
    wiso
    #
    @15
    @55
    wceq
    @56
    @11
    @29
    wceq
    @16
    @57
    wb
    @54
    @14
    @11
    @29
    clt
    clt
    @15
    isoeq5
    ax-mp
    @14
    @29
    clt
    clt
    @55
    @15
    isoeq1
    syl5bb
    cbviotav
    vw
    vx
    cr
    @21
    vx
    cv
    #
    cB
    @58
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
    @2
    @58
    wceq
    #
    @2
    @58
    @20
    @62
    caddc
    @63
    id
    @63
    @19
    @61
    cT
    cmul
    @63
    @18
    @60
    cfl
    @63
    @17
    @59
    cT
    cdiv
    @2
    @58
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    vw
    vy
    @34
    @36
    @47
    cB
    wceq
    #
    cA
    @47
    cif
    @51
    @35
    @64
    @2
    @47
    cA
    @2
    @47
    cB
    eqeq1
    @51
    id
    ifbieq2d
    cbvmptv
    vz
    vx
    cr
    @42
    @45
    cQ
    cfv
    #
    @58
    @22
    cfv
    #
    @37
    cfv
    #
    cle
    wbr
    #
    vi
    @40
    crab
    #
    cr
    clt
    csup
    @32
    @58
    wceq
    #
    cr
    @41
    @69
    clt
    @70
    @41
    @31
    @67
    cle
    wbr
    #
    vj
    @40
    crab
    @69
    @70
    @39
    @71
    vj
    @40
    @70
    @38
    @67
    @31
    cle
    @70
    @33
    @66
    @37
    @32
    @58
    @22
    fveq2
    fveq2d
    breq2d
    rabbidv
    @71
    @68
    vj
    vi
    @40
    @30
    @45
    wceq
    @31
    @65
    @67
    cle
    @30
    @45
    cQ
    fveq2
    breq1d
    cbvrabv
    syl6eq
    supeq1d
    cbvmptv
    fourierdlem107
end
