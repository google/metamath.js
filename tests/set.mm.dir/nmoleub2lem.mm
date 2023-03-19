include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "adantlr.mm"
include "cngp.mm"
include "cbs.mm"
include "cr.mm"
include "cnlm.mm"
include "cclm.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "nlmngp.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wf.mm"
include "clmhm.mm"
include "eqid.mm"
include "lmhmf.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "crp.mm"
include "rerpdivcld.mm"
include "rexrd.mm"
include "cxr.mm"
include "cghm.mm"
include "lmghm.mm"
include "nmocl.mm"
include "syl3anc.mm"
include "cxmu.mm"
include "cmul.mm"
include "wceq.mm"
include "rpred.mm"
include "rexmul.mm"
include "recnd.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "eqtrd.mm"
include "xmulcld.mm"
include "rpxrd.mm"
include "nmoix.mm"
include "syl31anc.mm"
include "cc0.mm"
include "nmoge0.mm"
include "jca.mm"
include "simprr.mm"
include "xlemul2a.mm"
include "xrletrd.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "xlemul1.mm"
include "mpbird.mm"
include "simplr.mm"
include "expr.mm"
include "syld.mm"
include "ralrimiva.mm"
include "cpnf.mm"
include "c0g.mm"
include "simpr.mm"
include "adantr.mm"
include "nmolb2d.mm"
include "pnfge.mm"
include "breqtrrd.mm"
include "cmnf.mm"
include "wne.mm"
include "wo.mm"
include "ge0nemnf.mm"
include "xrnemnf.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "impbida.mm"

theorem nmoleub2lem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vz: setvar z
  let cO: class O
  let cB: class B
  assume nmoleub2.n: |- N = ( S normOp T )
  assume nmoleub2.v: |- V = ( Base ` S )
  assume nmoleub2.l: |- L = ( norm ` S )
  assume nmoleub2.m: |- M = ( norm ` T )
  assume nmoleub2.g: |- G = ( Scalar ` S )
  assume nmoleub2.w: |- K = ( Base ` G )
  assume nmoleub2.s: |- ( ph -> S e. ( NrmMod i^i CMod ) )
  assume nmoleub2.t: |- ( ph -> T e. ( NrmMod i^i CMod ) )
  assume nmoleub2.f: |- ( ph -> F e. ( S LMHom T ) )
  assume nmoleub2.a: |- ( ph -> A e. RR* )
  assume nmoleub2.r: |- ( ph -> R e. RR+ )
  assume nmoleub2lem.5: |- ( ( ph /\ A. x e. V ( ps -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) -> 0 <_ A )
  assume nmoleub2lem.6: |- ( ( ( ( ph /\ A. x e. V ( ps -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) /\ A e. RR ) /\ ( y e. V /\ y =/= ( 0g ` S ) ) ) -> ( M ` ( F ` y ) ) <_ ( A x. ( L ` y ) ) )
  assume nmoleub2lem.7: |- ( ( ph /\ x e. V ) -> ( ps -> ( L ` x ) <_ R ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint L x
  disjoint L y
  disjoint N x
  disjoint N y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  disjoint R x
  disjoint R y
  disjoint T y
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F r
  disjoint F z
  disjoint L r
  disjoint L z
  disjoint O y
  disjoint O z
  disjoint M r
  disjoint M z
  disjoint ph r
  disjoint ph z
  disjoint S z
  disjoint V z
  disjoint B r
  disjoint R r
  disjoint R z
  assert |- ( ph -> ( ( N ` F ) <_ A <-> A. x e. V ( ps -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) )

  proof
    wph
    cF
    cN
    cfv
    #
    cA
    cle
    wbr
    #
    wps
    vx
    cv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    cR
    cdiv
    co
    #
    cA
    cle
    wbr
    #
    wi
    #
    vx
    cV
    wral
    #
    wph
    @1
    wa
    #
    @7
    vx
    cV
    @9
    @2
    cV
    wcel
    #
    wa
    wps
    @2
    cL
    cfv
    #
    cR
    cle
    wbr
    #
    @6
    wph
    @10
    wps
    @12
    wi
    @1
    nmoleub2lem.7
    adantlr
    @9
    @10
    @12
    @6
    @9
    @10
    @12
    wa
    #
    wa
    #
    @5
    @0
    cA
    @14
    @5
    @14
    @4
    cR
    @14
    cT
    cngp
    wcel
    #
    @3
    cT
    cbs
    cfv
    #
    wcel
    @4
    cr
    wcel
    wph
    @15
    @1
    @13
    wph
    cT
    cnlm
    wcel
    @15
    wph
    cnlm
    cclm
    cin
    #
    cnlm
    cT
    cnlm
    cclm
    inss1
    #
    nmoleub2.t
    sseldi
    cT
    nlmngp
    syl
    #
    ad2antrr
    #
    @14
    cV
    @16
    @2
    cF
    wph
    cV
    @16
    cF
    wf
    #
    @1
    @13
    wph
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    @21
    nmoleub2.f
    cV
    @16
    cS
    cT
    cF
    nmoleub2.v
    @16
    eqid
    #
    lmhmf
    syl
    ad2antrr
    @9
    @10
    @12
    simprl
    #
    ffvelrnd
    @3
    cT
    cM
    @16
    @23
    nmoleub2.m
    nmcl
    syl2anc
    #
    wph
    cR
    crp
    wcel
    #
    @1
    @13
    nmoleub2.r
    ad2antrr
    #
    rerpdivcld
    #
    rexrd
    #
    wph
    @0
    cxr
    wcel
    #
    @1
    @13
    wph
    cS
    cngp
    wcel
    #
    @15
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @30
    wph
    cS
    cnlm
    wcel
    @31
    wph
    @17
    cnlm
    cS
    @18
    nmoleub2.s
    sseldi
    cS
    nlmngp
    syl
    #
    @19
    wph
    @22
    @32
    nmoleub2.f
    cS
    cT
    cF
    lmghm
    syl
    #
    cS
    cT
    cF
    cN
    nmoleub2.n
    nmocl
    syl3anc
    #
    ad2antrr
    #
    wph
    cA
    cxr
    wcel
    #
    @1
    @13
    nmoleub2.a
    ad2antrr
    @14
    @5
    @0
    cle
    wbr
    #
    @5
    cR
    cxmu
    co
    #
    @0
    cR
    cxmu
    co
    #
    cle
    wbr
    #
    @14
    @39
    @4
    @40
    cle
    @14
    @39
    @5
    cR
    cmul
    co
    #
    @4
    @14
    @5
    cr
    wcel
    cR
    cr
    wcel
    @39
    @42
    wceq
    @28
    @14
    cR
    @27
    rpred
    #
    @5
    cR
    rexmul
    syl2anc
    @14
    @4
    cR
    @14
    @4
    @25
    recnd
    @14
    cR
    @43
    recnd
    @14
    cR
    @27
    rpne0d
    divcan1d
    eqtrd
    @14
    @4
    @0
    @11
    cxmu
    co
    #
    @40
    @14
    @4
    @25
    rexrd
    @14
    @0
    @11
    @36
    @14
    @11
    @14
    @31
    @10
    @11
    cr
    wcel
    wph
    @31
    @1
    @13
    @33
    ad2antrr
    #
    @24
    @2
    cS
    cL
    cV
    nmoleub2.v
    nmoleub2.l
    nmcl
    syl2anc
    rexrd
    #
    xmulcld
    @14
    @0
    cR
    @36
    @14
    cR
    @27
    rpxrd
    #
    xmulcld
    @14
    @31
    @15
    @32
    @10
    @4
    @44
    cle
    wbr
    @45
    @20
    wph
    @32
    @1
    @13
    @34
    ad2antrr
    @24
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    @2
    nmoleub2.n
    nmoleub2.v
    nmoleub2.l
    nmoleub2.m
    nmoix
    syl31anc
    @14
    @11
    cxr
    wcel
    cR
    cxr
    wcel
    @30
    cc0
    @0
    cle
    wbr
    #
    wa
    #
    @12
    @44
    @40
    cle
    wbr
    @46
    @47
    wph
    @49
    @1
    @13
    wph
    @30
    @48
    @35
    wph
    @31
    @15
    @32
    @48
    @33
    @19
    @34
    cS
    cT
    cF
    cN
    nmoleub2.n
    nmoge0
    syl3anc
    jca
    ad2antrr
    @9
    @10
    @12
    simprr
    @11
    cR
    @0
    xlemul2a
    syl31anc
    xrletrd
    eqbrtrd
    @14
    @5
    cxr
    wcel
    @30
    @26
    @38
    @41
    wb
    @29
    @36
    @27
    @5
    @0
    cR
    xlemul1
    syl3anc
    mpbird
    wph
    @1
    @13
    simplr
    xrletrd
    expr
    syld
    ralrimiva
    wph
    @8
    wa
    #
    cA
    cr
    wcel
    #
    @1
    cA
    cpnf
    wceq
    #
    @50
    @51
    wa
    vy
    cA
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    cS
    c0g
    cfv
    #
    nmoleub2.n
    nmoleub2.v
    nmoleub2.l
    nmoleub2.m
    @53
    eqid
    wph
    @31
    @8
    @51
    @33
    ad2antrr
    wph
    @15
    @8
    @51
    @19
    ad2antrr
    wph
    @32
    @8
    @51
    @34
    ad2antrr
    @50
    @51
    simpr
    @50
    cc0
    cA
    cle
    wbr
    #
    @51
    nmoleub2lem.5
    adantr
    nmoleub2lem.6
    nmolb2d
    @50
    @52
    wa
    #
    @0
    cpnf
    cA
    cle
    @55
    @30
    @0
    cpnf
    cle
    wbr
    wph
    @30
    @8
    @52
    @35
    ad2antrr
    @0
    pnfge
    syl
    @50
    @52
    simpr
    breqtrrd
    @50
    @37
    cA
    cmnf
    wne
    #
    wa
    @51
    @52
    wo
    @50
    @37
    @56
    wph
    @37
    @8
    nmoleub2.a
    adantr
    #
    @50
    @37
    @54
    @56
    @57
    nmoleub2lem.5
    cA
    ge0nemnf
    syl2anc
    jca
    cA
    xrnemnf
    sylib
    mpjaodan
    impbida
end
