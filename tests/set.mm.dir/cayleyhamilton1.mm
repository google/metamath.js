include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cayleyhamilton.mm"
include "adantr.mm"
include "wi.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nfeq2.mm"
include "nfan.mm"
include "cco1.mm"
include "wral.mm"
include "crg.mm"
include "cbs.mm"
include "wb.mm"
include "crngring.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "c0g.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "syl.mm"
include "ad2antrl.mm"
include "feqmptd.mm"
include "a1i.mm"
include "breq12d.mm"
include "biimpa.mm"
include "adantl.mm"
include "gsumsmonply1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "ply1coe1eq.mm"
include "syl3anc.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "simpl.mm"
include "csb.mm"
include "breq1d.mm"
include "gsummoncoe1.mm"
include "csbfv.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "exp32.mm"
include "com12.mm"
include "mpd.mm"
include "expcomd.mm"
include "sylbird.mm"
include "imp31.mm"
include "oveq1d.mm"
include "mpteq2da.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "mpid.mm"

theorem cayleyhamilton1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vl: setvar l
  let vi: setvar i
  assume cayleyhamilton.a: |- A = ( N Mat R )
  assume cayleyhamilton.b: |- B = ( Base ` A )
  assume cayleyhamilton.0: |- .0. = ( 0g ` A )
  assume cayleyhamilton.c: |- C = ( N CharPlyMat R )
  assume cayleyhamilton.k: |- K = ( coe1 ` ( C ` M ) )
  assume cayleyhamilton.m: |- .* = ( .s ` A )
  assume cayleyhamilton.e: |- .^ = ( .g ` ( mulGrp ` A ) )
  assume cayleyhamilton1.l: |- L = ( Base ` R )
  assume cayleyhamilton1.x: |- X = ( var1 ` R )
  assume cayleyhamilton1.p: |- P = ( Poly1 ` R )
  assume cayleyhamilton1.m: |- .x. = ( .s ` P )
  assume cayleyhamilton1.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume cayleyhamilton1.z: |- Z = ( 0g ` R )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint .* n
  disjoint .^ n
  disjoint E n
  disjoint F n
  disjoint L n
  disjoint P n
  disjoint X n
  disjoint Z n
  disjoint .x. n
  disjoint A b
  disjoint A m
  disjoint A s
  disjoint A x
  disjoint A y
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint B b
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint K b
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M m
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint M l
  disjoint b l
  disjoint l n
  disjoint l s
  disjoint l x
  disjoint l y
  disjoint N b
  disjoint N m
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint N l
  disjoint R b
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint R l
  disjoint .0. b
  disjoint .0. s
  disjoint .0. x
  disjoint .0. y
  disjoint .* m
  disjoint .* s
  disjoint .* x
  disjoint .* y
  disjoint .* b
  disjoint .^ b
  disjoint .^ m
  disjoint .^ s
  disjoint .^ x
  disjoint .^ y
  disjoint B i
  disjoint C m
  disjoint E i
  disjoint E m
  disjoint i m
  disjoint i n
  disjoint F i
  disjoint F m
  disjoint K m
  disjoint L i
  disjoint M i
  disjoint N i
  disjoint P i
  disjoint P m
  disjoint R i
  disjoint X i
  disjoint X m
  disjoint Z i
  disjoint .x. i
  disjoint .x. m
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( F e. ( L ^m NN0 ) /\ F finSupp Z ) ) -> ( ( C ` M ) = ( P gsum ( n e. NN0 |-> ( ( F ` n ) .x. ( n E X ) ) ) ) -> ( A gsum ( n e. NN0 |-> ( ( F ` n ) .* ( n .^ M ) ) ) ) = .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cF
    cL
    cn0
    cmap
    co
    wcel
    #
    cF
    cZ
    cfsupp
    wbr
    #
    wa
    #
    wa
    #
    cM
    cC
    cfv
    #
    cP
    vn
    cn0
    vn
    cv
    #
    cF
    cfv
    #
    @9
    cX
    cE
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    cA
    vn
    cn0
    @9
    cK
    cfv
    #
    @9
    cM
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    wceq
    #
    cA
    vn
    cn0
    @10
    @17
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    wceq
    #
    @3
    @21
    @6
    cA
    cB
    cC
    cR
    vn
    c.ex
    c.as
    cK
    cM
    cN
    c.0
    cayleyhamilton.a
    cayleyhamilton.b
    cayleyhamilton.0
    cayleyhamilton.c
    cayleyhamilton.k
    cayleyhamilton.m
    cayleyhamilton.e
    cayleyhamilton
    adantr
    @7
    @15
    @21
    @25
    wi
    @7
    @15
    wa
    #
    @21
    @25
    @26
    @20
    @24
    c.0
    @26
    @19
    @23
    cA
    cgsu
    @26
    vn
    cn0
    @18
    @22
    @7
    @15
    vn
    @7
    vn
    nfv
    vn
    @8
    @14
    vn
    cP
    @13
    cgsu
    vn
    cP
    nfcv
    vn
    cgsu
    nfcv
    vn
    cn0
    @12
    nfmpt1
    nfov
    nfeq2
    nfan
    @26
    @9
    cn0
    wcel
    #
    wa
    @16
    @10
    @17
    c.as
    @7
    @15
    @27
    @16
    @10
    wceq
    #
    @7
    @15
    vm
    cv
    #
    cK
    cfv
    #
    @29
    cP
    vi
    cn0
    vi
    cv
    #
    cF
    cfv
    #
    @31
    cX
    cE
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    vm
    cn0
    wral
    #
    @27
    @28
    wi
    @7
    cR
    crg
    wcel
    #
    @8
    cP
    cbs
    cfv
    #
    wcel
    #
    @14
    @42
    wcel
    @40
    @15
    wb
    @3
    @41
    @6
    @1
    @0
    @41
    @2
    cR
    crngring
    3ad2ant2
    #
    adantr
    #
    @3
    @43
    @6
    cA
    cB
    cC
    cP
    cR
    @42
    cM
    cN
    cayleyhamilton.c
    cayleyhamilton.a
    cayleyhamilton.b
    cayleyhamilton1.p
    @42
    eqid
    #
    chpmatply1
    adantr
    @7
    @10
    @42
    cP
    cR
    vn
    cE
    c.x
    cL
    cX
    cR
    c0g
    cfv
    #
    cayleyhamilton1.p
    @46
    cayleyhamilton1.x
    cayleyhamilton1.e
    @45
    cayleyhamilton1.l
    cayleyhamilton1.m
    @47
    eqid
    @4
    @10
    cL
    wcel
    #
    vn
    cn0
    wral
    #
    @3
    @5
    @4
    cn0
    cL
    cF
    wf
    #
    @49
    cF
    cL
    cn0
    elmapi
    #
    @50
    @48
    vn
    cn0
    cn0
    cL
    @9
    cF
    ffvelrn
    ralrimiva
    syl
    ad2antrl
    @6
    vn
    cn0
    @10
    cmpt
    #
    @47
    cfsupp
    wbr
    #
    @3
    @4
    @5
    @53
    @4
    cF
    @52
    cZ
    @47
    cfsupp
    @4
    vn
    cn0
    cL
    cF
    @51
    feqmptd
    cZ
    @47
    wceq
    @4
    cayleyhamilton1.z
    a1i
    breq12d
    biimpa
    adantl
    gsumsmonply1
    cK
    @42
    @37
    cP
    cR
    vm
    @8
    @14
    cayleyhamilton1.p
    @46
    cayleyhamilton.k
    @36
    @14
    cco1
    @35
    @13
    cP
    cgsu
    vi
    vn
    cn0
    @34
    @12
    @31
    @9
    wceq
    @32
    @10
    @33
    @11
    c.x
    @31
    @9
    cF
    fveq2
    @31
    @9
    cX
    cE
    oveq1
    oveq12d
    cbvmptv
    oveq2i
    fveq2i
    ply1coe1eq
    syl3anc
    @7
    @27
    @40
    @28
    @27
    @40
    wa
    #
    @7
    @28
    @54
    @16
    @9
    @37
    cfv
    #
    wceq
    #
    @7
    @28
    wi
    #
    @39
    @56
    vm
    @9
    cn0
    @29
    @9
    wceq
    @30
    @16
    @38
    @55
    @29
    @9
    cK
    fveq2
    @29
    @9
    @37
    fveq2
    eqeq12d
    rspcva
    @27
    @56
    @57
    wi
    @40
    @56
    @27
    @57
    @56
    @27
    @7
    @28
    @56
    @27
    @7
    wa
    #
    wa
    @16
    @55
    @10
    @56
    @58
    simpl
    @58
    @55
    @10
    wceq
    @56
    @58
    @55
    vi
    @9
    @32
    csb
    @10
    @58
    @32
    @42
    cP
    cR
    vi
    cE
    c.x
    cL
    @9
    cX
    cZ
    cayleyhamilton1.p
    @46
    cayleyhamilton1.x
    cayleyhamilton1.e
    @3
    @41
    @27
    @6
    @44
    ad2antrl
    cayleyhamilton1.l
    cayleyhamilton1.m
    cayleyhamilton1.z
    @7
    @32
    cL
    wcel
    #
    vi
    cn0
    wral
    #
    @27
    @4
    @60
    @3
    @5
    @4
    @50
    @60
    @51
    @50
    @59
    vi
    cn0
    cn0
    cL
    @31
    cF
    ffvelrn
    ralrimiva
    syl
    ad2antrl
    adantl
    @7
    vi
    cn0
    @32
    cmpt
    #
    cZ
    cfsupp
    wbr
    #
    @27
    @6
    @62
    @3
    @4
    @5
    @62
    @4
    cF
    @61
    cZ
    cfsupp
    @4
    vi
    cn0
    cL
    cF
    @51
    feqmptd
    breq1d
    biimpa
    adantl
    adantl
    @27
    @7
    simpl
    gsummoncoe1
    vi
    @9
    cF
    csbfv
    syl6eq
    adantl
    eqtrd
    exp32
    com12
    adantr
    mpd
    com12
    expcomd
    sylbird
    imp31
    oveq1d
    mpteq2da
    oveq2d
    eqeq1d
    biimpd
    ex
    mpid
end
