include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "adantr.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "cmul.mm"
include "cvsca.mm"
include "csca.mm"
include "cnm.mm"
include "clmhm.mm"
include "ad3antrrr.mm"
include "wss.mm"
include "crp.mm"
include "cngp.mm"
include "cnlm.mm"
include "cclm.mm"
include "elin1d.mm"
include "nlmngp.mm"
include "syl.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "nmrpcl.mm"
include "syl3anc.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "sseldd.mm"
include "lmhmlin.mm"
include "fveq2d.mm"
include "cbs.mm"
include "lmhmsca.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "wf.mm"
include "lmhmf.mm"
include "ffvelrnd.mm"
include "nmvs.mm"
include "fveq1d.mm"
include "cabs.mm"
include "elin2d.mm"
include "clmabs.mm"
include "syl2anc.mm"
include "rpge0d.mm"
include "absidd.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "rpcnd.mm"
include "nmcl.mm"
include "recnd.mm"
include "rpne0d.mm"
include "divassd.mm"
include "dmdcand.mm"
include "clmvscl.mm"
include "simpllr.mm"
include "divcan1d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "eqbrtrrd.mm"
include "simplr.mm"
include "ledivmul2d.mm"
include "mpbid.mm"
include "leidd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "nmoleub2lem.mm"

theorem nmoleub3
  let wph: wff ph
  let vx: setvar x
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
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let wps: wff ps
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
  assume nmoleub3.5: |- ( ph -> 0 <_ A )
  assume nmoleub3.6: |- ( ph -> RR C_ K )

  disjoint A x
  disjoint F x
  disjoint L x
  disjoint N x
  disjoint M x
  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint R x
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F r
  disjoint F y
  disjoint F z
  disjoint L r
  disjoint L y
  disjoint L z
  disjoint N y
  disjoint O y
  disjoint O z
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint ps y
  disjoint S y
  disjoint S z
  disjoint V y
  disjoint V z
  disjoint B r
  disjoint R r
  disjoint R y
  disjoint R z
  disjoint T y
  assert |- ( ph -> ( ( N ` F ) <_ A <-> A. x e. V ( ( L ` x ) = R -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) )

  proof
    wph
    vx
    cv
    #
    cL
    cfv
    #
    cR
    wceq
    #
    vx
    vy
    cA
    cR
    cS
    cT
    cF
    cG
    cK
    cL
    cM
    cN
    cV
    nmoleub2.n
    nmoleub2.v
    nmoleub2.l
    nmoleub2.m
    nmoleub2.g
    nmoleub2.w
    nmoleub2.s
    nmoleub2.t
    nmoleub2.f
    nmoleub2.a
    nmoleub2.r
    wph
    cc0
    cA
    cle
    wbr
    @2
    @0
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
    nmoleub3.5
    adantr
    wph
    @8
    wa
    #
    cA
    cr
    wcel
    #
    wa
    #
    vy
    cv
    #
    cV
    wcel
    #
    @12
    cS
    c0g
    cfv
    #
    wne
    #
    wa
    #
    wa
    #
    @12
    cF
    cfv
    #
    cM
    cfv
    #
    @12
    cL
    cfv
    #
    cdiv
    co
    #
    cA
    cle
    wbr
    @19
    cA
    @20
    cmul
    co
    cle
    wbr
    @17
    cR
    @20
    cdiv
    co
    #
    @12
    cS
    cvsca
    cfv
    #
    co
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
    @21
    cA
    cle
    @17
    @27
    @22
    @19
    cmul
    co
    #
    cR
    cdiv
    co
    @22
    @19
    cR
    cdiv
    co
    cmul
    co
    @21
    @17
    @26
    @28
    cR
    cdiv
    @17
    @26
    @22
    @18
    cT
    cvsca
    cfv
    #
    co
    #
    cM
    cfv
    #
    @22
    cT
    csca
    cfv
    #
    cnm
    cfv
    #
    cfv
    #
    @19
    cmul
    co
    #
    @28
    @17
    @25
    @30
    cM
    @17
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    @22
    cK
    wcel
    #
    @13
    @25
    @30
    wceq
    wph
    @36
    @8
    @10
    @16
    nmoleub2.f
    ad3antrrr
    #
    @17
    cr
    cK
    @22
    wph
    cr
    cK
    wss
    @8
    @10
    @16
    nmoleub3.6
    ad3antrrr
    @17
    @22
    @17
    cR
    @20
    wph
    cR
    crp
    wcel
    #
    @8
    @10
    @16
    nmoleub2.r
    ad3antrrr
    #
    @17
    cS
    cngp
    wcel
    #
    @13
    @15
    @20
    crp
    wcel
    @17
    cS
    cnlm
    wcel
    #
    @41
    wph
    @42
    @8
    @10
    @16
    wph
    cnlm
    cclm
    cS
    nmoleub2.s
    elin1d
    ad3antrrr
    #
    cS
    nlmngp
    syl
    @11
    @13
    @15
    simprl
    #
    @11
    @13
    @15
    simprr
    @12
    cS
    cL
    cV
    @14
    nmoleub2.v
    nmoleub2.l
    @14
    eqid
    nmrpcl
    syl3anc
    #
    rpdivcld
    #
    rpred
    #
    sseldd
    #
    @44
    cK
    cS
    cT
    @23
    @29
    cV
    cF
    cG
    @22
    @12
    nmoleub2.g
    nmoleub2.w
    nmoleub2.v
    @23
    eqid
    #
    @29
    eqid
    #
    lmhmlin
    syl3anc
    fveq2d
    @17
    cT
    cnlm
    wcel
    #
    @22
    @32
    cbs
    cfv
    #
    wcel
    @18
    cT
    cbs
    cfv
    #
    wcel
    #
    @31
    @35
    wceq
    wph
    @51
    @8
    @10
    @16
    wph
    cnlm
    cclm
    cT
    nmoleub2.t
    elin1d
    ad3antrrr
    #
    @17
    @22
    cK
    @52
    @48
    @17
    @52
    cG
    cbs
    cfv
    cK
    @17
    @32
    cG
    cbs
    @17
    @36
    @32
    cG
    wceq
    @38
    cS
    cT
    cF
    cG
    @32
    nmoleub2.g
    @32
    eqid
    #
    lmhmsca
    syl
    #
    fveq2d
    nmoleub2.w
    syl6eqr
    eleqtrrd
    @17
    cV
    @53
    @12
    cF
    @17
    @36
    cV
    @53
    cF
    wf
    @38
    cV
    @53
    cS
    cT
    cF
    nmoleub2.v
    @53
    eqid
    #
    lmhmf
    syl
    @44
    ffvelrnd
    #
    @33
    @29
    @32
    @52
    cM
    @53
    cT
    @22
    @18
    @58
    nmoleub2.m
    @50
    @56
    @52
    eqid
    @33
    eqid
    nmvs
    syl3anc
    @17
    @34
    @22
    @19
    cmul
    @17
    @34
    @22
    cG
    cnm
    cfv
    #
    cfv
    #
    @22
    @17
    @22
    @33
    @60
    @17
    @32
    cG
    cnm
    @57
    fveq2d
    fveq1d
    @17
    @22
    cabs
    cfv
    #
    @61
    @22
    @17
    cS
    cclm
    wcel
    #
    @37
    @62
    @61
    wceq
    wph
    @63
    @8
    @10
    @16
    wph
    cnlm
    cclm
    cS
    nmoleub2.s
    elin2d
    ad3antrrr
    #
    @48
    @22
    cG
    cK
    cS
    nmoleub2.g
    nmoleub2.w
    clmabs
    syl2anc
    @17
    @22
    @47
    @17
    @22
    @46
    rpge0d
    absidd
    eqtr3d
    #
    eqtrd
    oveq1d
    3eqtrd
    oveq1d
    @17
    @22
    @19
    cR
    @17
    @22
    @46
    rpcnd
    @17
    @19
    @17
    cT
    cngp
    wcel
    #
    @54
    @19
    cr
    wcel
    @17
    @51
    @66
    @55
    cT
    nlmngp
    syl
    @59
    @18
    cT
    cM
    @53
    @58
    nmoleub2.m
    nmcl
    syl2anc
    #
    recnd
    #
    @17
    cR
    @40
    rpcnd
    #
    @17
    cR
    @40
    rpne0d
    #
    divassd
    @17
    @19
    cR
    @20
    @68
    @69
    @17
    @20
    @45
    rpcnd
    #
    @70
    @17
    @20
    @45
    rpne0d
    #
    dmdcand
    3eqtrd
    @17
    @24
    cV
    wcel
    #
    @8
    @24
    cL
    cfv
    #
    cR
    wceq
    #
    @27
    cA
    cle
    wbr
    #
    @17
    @63
    @37
    @13
    @73
    @64
    @48
    @44
    @22
    @23
    cG
    cK
    cV
    cS
    @12
    nmoleub2.v
    nmoleub2.g
    @49
    nmoleub2.w
    clmvscl
    syl3anc
    wph
    @8
    @10
    @16
    simpllr
    @17
    @74
    @61
    @20
    cmul
    co
    #
    @22
    @20
    cmul
    co
    cR
    @17
    @42
    @37
    @13
    @74
    @77
    wceq
    @43
    @48
    @44
    @60
    @23
    cG
    cK
    cL
    cV
    cS
    @22
    @12
    nmoleub2.v
    nmoleub2.l
    @49
    nmoleub2.g
    nmoleub2.w
    @60
    eqid
    nmvs
    syl3anc
    @17
    @61
    @22
    @20
    cmul
    @65
    oveq1d
    @17
    cR
    @20
    @69
    @71
    @72
    divcan1d
    3eqtrd
    @7
    @75
    @76
    wi
    vx
    @24
    cV
    @0
    @24
    wceq
    #
    @2
    @75
    @6
    @76
    @78
    @1
    @74
    cR
    @0
    @24
    cL
    fveq2
    eqeq1d
    @78
    @5
    @27
    cA
    cle
    @78
    @4
    @26
    cR
    cdiv
    @78
    @3
    @25
    cM
    @0
    @24
    cF
    fveq2
    fveq2d
    oveq1d
    breq1d
    imbi12d
    rspcv
    syl3c
    eqbrtrrd
    @17
    @19
    cA
    @20
    @67
    @9
    @10
    @16
    simplr
    @45
    ledivmul2d
    mpbid
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @1
    cR
    cle
    wbr
    @2
    cR
    cR
    cle
    wbr
    @80
    cR
    @80
    cR
    wph
    @39
    @79
    nmoleub2.r
    adantr
    rpred
    leidd
    @1
    cR
    cR
    cle
    breq1
    syl5ibrcom
    nmoleub2lem
end
