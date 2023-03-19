include "cc0.mm"
include "cpr.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
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
include "cmin.mm"
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
include "oveq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "uneq2i.mm"
include "isoeq1.mm"
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
include "fourierdlem100.mm"

theorem fourierdlem105
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cL: class L
  let cM: class M
  let vp: setvar p
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  assume fourierdlem105.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem105.t: |- T = ( B - A )
  assume fourierdlem105.m: |- ( ph -> M e. NN )
  assume fourierdlem105.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem105.f: |- ( ph -> F : RR --> CC )
  assume fourierdlem105.6: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem105.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem105.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem105.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )
  assume fourierdlem105.c: |- ( ph -> C e. RR )
  assume fourierdlem105.d: |- ( ph -> D e. ( C (,) +oo ) )

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
  disjoint C i
  disjoint C x
  disjoint C m
  disjoint C p
  disjoint D i
  disjoint D x
  disjoint D m
  disjoint D p
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
  disjoint i ph
  disjoint ph x
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint j k
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint i j
  disjoint i k
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint j x
  disjoint k x
  disjoint w x
  disjoint x y
  disjoint x z
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
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C w
  disjoint C y
  disjoint f g
  disjoint g k
  disjoint g w
  disjoint g y
  disjoint g i
  disjoint g x
  disjoint D f
  disjoint D g
  disjoint D k
  disjoint D w
  disjoint D y
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
  disjoint Q j
  disjoint Q k
  disjoint Q w
  disjoint Q y
  disjoint g j
  disjoint Q z
  disjoint R y
  disjoint T f
  disjoint T g
  disjoint T j
  disjoint T k
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint g p
  disjoint k x
  assert |- ( ph -> ( x e. ( C [,] D ) |-> ( F ` x ) ) e. L^1 )

  proof
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cc0
    cC
    cD
    cpr
    #
    vw
    cv
    #
    vj
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
    vj
    cz
    wrex
    #
    vw
    cC
    cD
    cicc
    co
    #
    crab
    #
    cun
    #
    chash
    cfv
    c1
    cmin
    co
    #
    cfz
    co
    #
    @10
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
    cmpt
    #
    cF
    @10
    vz
    cr
    @2
    cQ
    cfv
    #
    vz
    cv
    #
    @20
    cfv
    #
    vw
    cA
    cB
    cioc
    co
    #
    @1
    cB
    wceq
    #
    cA
    @1
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
    @27
    cL
    cM
    @11
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
    @33
    cfv
    cD
    wceq
    wa
    vi
    cv
    #
    @33
    cfv
    @35
    c1
    caddc
    co
    @33
    cfv
    clt
    wbr
    vi
    cc0
    @34
    cfzo
    co
    wral
    wa
    vp
    cr
    cc0
    @34
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    vp
    fourierdlem105.p
    fourierdlem105.t
    fourierdlem105.m
    fourierdlem105.q
    fourierdlem105.f
    fourierdlem105.6
    fourierdlem105.fcn
    fourierdlem105.r
    fourierdlem105.l
    fourierdlem105.c
    fourierdlem105.d
    @36
    eqid
    @11
    eqid
    @9
    vy
    cv
    #
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
    @5
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @8
    crab
    @0
    @7
    @42
    vw
    vy
    @8
    @1
    @37
    wceq
    #
    @7
    @37
    @3
    caddc
    co
    #
    @5
    wcel
    #
    vj
    cz
    wrex
    @42
    @43
    @6
    @45
    vj
    cz
    @43
    @4
    @44
    @5
    @1
    @37
    @3
    caddc
    oveq1
    eleq1d
    rexbidv
    @45
    @41
    vj
    vk
    cz
    @2
    @38
    wceq
    #
    @44
    @40
    @5
    @46
    @3
    @39
    @37
    caddc
    @2
    @38
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    cbvrexv
    syl6bb
    cbvrabv
    uneq2i
    @14
    @12
    @10
    clt
    clt
    vf
    cv
    #
    wiso
    vg
    vf
    @12
    @10
    clt
    clt
    @47
    @13
    isoeq1
    cbviotav
    vw
    vx
    cr
    @19
    vx
    cv
    #
    cB
    @48
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
    @48
    wceq
    #
    @1
    @48
    @18
    @52
    caddc
    @53
    id
    @53
    @17
    @51
    cT
    cmul
    @53
    @16
    @50
    cfl
    @53
    @15
    @49
    cT
    cdiv
    @1
    @48
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
    @24
    @26
    @37
    cB
    wceq
    #
    cA
    @37
    cif
    @43
    @25
    @54
    @1
    @37
    cA
    @1
    @37
    cB
    eqeq1
    @43
    id
    ifbieq2d
    cbvmptv
    vz
    vx
    cr
    @32
    @35
    cQ
    cfv
    #
    @48
    @20
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
    @22
    @48
    wceq
    #
    cr
    @31
    @59
    clt
    @60
    @31
    @21
    @57
    cle
    wbr
    #
    vj
    @30
    crab
    @59
    @60
    @29
    @61
    vj
    @30
    @60
    @28
    @57
    @21
    cle
    @60
    @23
    @56
    @27
    @22
    @48
    @20
    fveq2
    fveq2d
    breq2d
    rabbidv
    @61
    @58
    vj
    vi
    @30
    @2
    @35
    wceq
    @21
    @55
    @57
    cle
    @2
    @35
    cQ
    fveq2
    breq1d
    cbvrabv
    syl6eq
    supeq1d
    cbvmptv
    fourierdlem100
end
