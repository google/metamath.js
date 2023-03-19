include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "c0g.mm"
include "cc0.mm"
include "wceq.mm"
include "clmhm.mm"
include "wcel.mm"
include "cghm.mm"
include "lmghm.mm"
include "eqid.mm"
include "ghmid.mm"
include "3syl.mm"
include "fveq2d.mm"
include "cnlm.mm"
include "cngp.mm"
include "cclm.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "nlmngp.mm"
include "nm0.mm"
include "eqtrd.mm"
include "adantr.mm"
include "oveq1d.mm"
include "crp.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "div0d.mm"
include "clt.mm"
include "cgrp.mm"
include "syl.mm"
include "ngpgrp.mm"
include "grpidcl.mm"
include "cr.mm"
include "nmcl.mm"
include "sylan.mm"
include "rpred.mm"
include "syl2anc.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "imp.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "eqbrtrrd.mm"
include "wne.mm"
include "cmul.mm"
include "wn.mm"
include "cvsca.mm"
include "simp-4l.mm"
include "cxr.mm"
include "cq.mm"
include "wss.mm"
include "simpllr.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "rspccv.mm"
include "simpr.mm"
include "nmoleub2lem3.mm"
include "iman.mm"
include "mpbir.mm"
include "nmoleub2lem.mm"

theorem nmoleub2lem2
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
  let cO: class O
  let cV: class V
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
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
  assume nmoleub2a.5: |- ( ph -> QQ C_ K )
  assume nmoleub2lem2.6: |- ( ( ( L ` x ) e. RR /\ R e. RR ) -> ( ( L ` x ) O R -> ( L ` x ) <_ R ) )
  assume nmoleub2lem2.7: |- ( ( ( L ` x ) e. RR /\ R e. RR ) -> ( ( L ` x ) < R -> ( L ` x ) O R ) )

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
  assert |- ( ph -> ( ( N ` F ) <_ A <-> A. x e. V ( ( L ` x ) O R -> ( ( M ` ( F ` x ) ) / R ) <_ A ) ) )

  proof
    wph
    vx
    cv
    #
    cL
    cfv
    #
    cR
    cO
    wbr
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
    wa
    #
    cS
    c0g
    cfv
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
    cc0
    cA
    cle
    @9
    @13
    cc0
    cR
    cdiv
    co
    cc0
    @9
    @12
    cc0
    cR
    cdiv
    wph
    @12
    cc0
    wceq
    @8
    wph
    @12
    cT
    c0g
    cfv
    #
    cM
    cfv
    #
    cc0
    wph
    @11
    @14
    cM
    wph
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    @11
    @14
    wceq
    nmoleub2.f
    cS
    cT
    cF
    lmghm
    cS
    cT
    cF
    @10
    @14
    @10
    eqid
    #
    @14
    eqid
    #
    ghmid
    3syl
    fveq2d
    wph
    cT
    cnlm
    wcel
    cT
    cngp
    wcel
    @15
    cc0
    wceq
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
    cT
    cM
    @14
    nmoleub2.m
    @18
    nm0
    3syl
    eqtrd
    adantr
    oveq1d
    @9
    cR
    @9
    cR
    wph
    cR
    crp
    wcel
    #
    @8
    nmoleub2.r
    adantr
    #
    rpcnd
    @9
    cR
    @22
    rpne0d
    div0d
    eqtrd
    @9
    @10
    cV
    wcel
    #
    @1
    cR
    clt
    wbr
    #
    @6
    wi
    #
    vx
    cV
    wral
    #
    @10
    cL
    cfv
    #
    cR
    clt
    wbr
    #
    @13
    cA
    cle
    wbr
    #
    wph
    @23
    @8
    wph
    cS
    cngp
    wcel
    #
    cS
    cgrp
    wcel
    @23
    wph
    cS
    cnlm
    wcel
    #
    @30
    wph
    @19
    cnlm
    cS
    @20
    nmoleub2.s
    sseldi
    #
    cS
    nlmngp
    #
    syl
    #
    cS
    ngpgrp
    cV
    cS
    @10
    nmoleub2.v
    @17
    grpidcl
    3syl
    adantr
    wph
    @8
    @26
    wph
    @7
    @25
    vx
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @24
    @2
    @6
    @36
    @1
    cr
    wcel
    #
    cR
    cr
    wcel
    #
    @24
    @2
    wi
    wph
    @30
    @35
    @37
    @34
    @0
    cS
    cL
    cV
    nmoleub2.v
    nmoleub2.l
    nmcl
    sylan
    #
    @36
    cR
    wph
    @21
    @35
    nmoleub2.r
    adantr
    rpred
    #
    nmoleub2lem2.7
    syl2anc
    imim1d
    ralimdva
    imp
    #
    @9
    @27
    cc0
    cR
    clt
    wph
    @27
    cc0
    wceq
    #
    @8
    wph
    @31
    @30
    @42
    @32
    @33
    cS
    cL
    @10
    nmoleub2.l
    @17
    nm0
    3syl
    adantr
    @9
    cR
    @22
    rpgt0d
    eqbrtrd
    @25
    @28
    @29
    wi
    vx
    @10
    cV
    @0
    @10
    wceq
    #
    @24
    @28
    @6
    @29
    @43
    @1
    @27
    cR
    clt
    @0
    @10
    cL
    fveq2
    breq1d
    @43
    @5
    @13
    cA
    cle
    @43
    @4
    @12
    cR
    cdiv
    @43
    @3
    @11
    cM
    @0
    @10
    cF
    fveq2
    fveq2d
    oveq1d
    breq1d
    imbi12d
    rspcv
    syl3c
    eqbrtrrd
    #
    @9
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
    @47
    @10
    wne
    #
    wa
    #
    wa
    #
    @47
    cF
    cfv
    cM
    cfv
    cA
    @47
    cL
    cfv
    cmul
    co
    cle
    wbr
    #
    wi
    @51
    @52
    wn
    #
    wa
    #
    wn
    @54
    cA
    @47
    cR
    cS
    cT
    cS
    cvsca
    cfv
    #
    cF
    cG
    cK
    cL
    cM
    cN
    cV
    vz
    nmoleub2.n
    nmoleub2.v
    nmoleub2.l
    nmoleub2.m
    nmoleub2.g
    nmoleub2.w
    @54
    wph
    cS
    @19
    wcel
    wph
    @8
    @45
    @50
    @53
    simp-4l
    #
    nmoleub2.s
    syl
    @54
    wph
    cT
    @19
    wcel
    @56
    nmoleub2.t
    syl
    @54
    wph
    @16
    @56
    nmoleub2.f
    syl
    @54
    wph
    cA
    cxr
    wcel
    @56
    nmoleub2.a
    syl
    @54
    wph
    @21
    @56
    nmoleub2.r
    syl
    @54
    wph
    cq
    cK
    wss
    @56
    nmoleub2a.5
    syl
    @55
    eqid
    @9
    @45
    @50
    @53
    simpllr
    @9
    cc0
    cA
    cle
    wbr
    @45
    @50
    @53
    @44
    ad3antrrr
    @46
    @48
    @49
    @53
    simplrl
    @46
    @48
    @49
    @53
    simplrr
    @54
    @26
    vz
    cv
    @47
    @55
    co
    #
    cV
    wcel
    @57
    cL
    cfv
    #
    cR
    clt
    wbr
    #
    @57
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
    wi
    @9
    @26
    @45
    @50
    @53
    @41
    ad3antrrr
    @25
    @64
    vx
    @57
    cV
    @0
    @57
    wceq
    #
    @24
    @59
    @6
    @63
    @65
    @1
    @58
    cR
    clt
    @0
    @57
    cL
    fveq2
    breq1d
    @65
    @5
    @62
    cA
    cle
    @65
    @4
    @61
    cR
    cdiv
    @65
    @3
    @60
    cM
    @0
    @57
    cF
    fveq2
    fveq2d
    oveq1d
    breq1d
    imbi12d
    rspccv
    syl
    @51
    @53
    simpr
    nmoleub2lem3
    @51
    @52
    iman
    mpbir
    @36
    @37
    @38
    @2
    @1
    cR
    cle
    wbr
    wi
    @39
    @40
    nmoleub2lem2.6
    syl2anc
    nmoleub2lem
end
