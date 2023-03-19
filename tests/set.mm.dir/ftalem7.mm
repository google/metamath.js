include "cfv.mm"
include "cabs.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cc.mm"
include "wrex.mm"
include "wral.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "clt.mm"
include "ccoe.mm"
include "cdgr.mm"
include "eqid.mm"
include "cidp.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "ccom.mm"
include "cply.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "addcld.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "negcld.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "df-idp.mm"
include "mptresid.mm"
include "eqtr4i.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "id.mm"
include "subneg.mm"
include "syl2anr.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "plyssc.mm"
include "sseldi.mm"
include "c1.mm"
include "ccnv.mm"
include "cima.mm"
include "w3a.mm"
include "plyremlem.mm"
include "simp1d.mm"
include "addcl.mm"
include "adantl.mm"
include "cmul.mm"
include "mulcl.mm"
include "plyco.mm"
include "eqeltrrd.mm"
include "cn.mm"
include "fveq2d.mm"
include "dgrco.mm"
include "simp2d.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "nnmulcld.mm"
include "eqeltrd.mm"
include "0cn.mm"
include "oveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "addid2d.mm"
include "syl5eq.mm"
include "eqnetrd.mm"
include "ftalem6.mm"
include "breq12d.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "cr.mm"
include "ltnled.mm"
include "bitrd.mm"
include "biimpd.mm"
include "breq2d.mm"
include "notbid.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "rexnal.mm"
include "sylib.mm"

theorem ftalem7
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cF: class F
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cD: class D
  let cE: class E
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let cJ: class J
  let cR: class R
  let cT: class T
  let cU: class U
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem7.5: |- ( ph -> X e. CC )
  assume ftalem7.6: |- ( ph -> ( F ` X ) =/= 0 )

  disjoint A x
  disjoint N x
  disjoint F x
  disjoint ph x
  disjoint X x
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k x
  disjoint A k
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint s z
  disjoint D s
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint E r
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint N r
  disjoint N s
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s w
  disjoint s y
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J s
  disjoint J x
  disjoint J z
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S k
  disjoint S s
  disjoint T k
  disjoint T r
  disjoint T x
  disjoint U r
  disjoint U x
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ph -> -. A. x e. CC ( abs ` ( F ` X ) ) <_ ( abs ` ( F ` x ) ) )

  proof
    wph
    cX
    cF
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wn
    #
    vx
    cc
    wrex
    #
    @5
    vx
    cc
    wral
    wn
    wph
    vy
    cv
    #
    vz
    cc
    vz
    cv
    #
    cX
    caddc
    co
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    #
    cabs
    cfv
    #
    cc0
    @12
    cfv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    vy
    cc
    wrex
    @7
    wph
    vy
    @12
    ccoe
    cfv
    #
    cc
    @12
    @12
    cdgr
    cfv
    #
    @18
    eqid
    @19
    eqid
    wph
    cF
    cidp
    cc
    cX
    cneg
    #
    csn
    #
    cxp
    #
    cmin
    cof
    co
    #
    ccom
    #
    @12
    cc
    cply
    cfv
    #
    wph
    vz
    vy
    cc
    cc
    @10
    @8
    cF
    cfv
    @11
    @23
    cF
    wph
    @9
    cc
    wcel
    #
    wa
    @9
    cX
    wph
    @26
    simpr
    #
    wph
    cX
    cc
    wcel
    #
    @26
    ftalem7.5
    adantr
    addcld
    wph
    @23
    vz
    cc
    @9
    @20
    cmin
    co
    #
    cmpt
    vz
    cc
    @10
    cmpt
    wph
    vz
    cc
    @9
    @20
    cmin
    cidp
    @22
    cvv
    cc
    cc
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    @27
    wph
    @20
    cc
    wcel
    #
    @26
    wph
    cX
    ftalem7.5
    negcld
    #
    adantr
    cidp
    vz
    cc
    @9
    cmpt
    #
    wceq
    wph
    cidp
    cid
    cc
    cres
    @32
    df-idp
    vz
    cc
    mptresid
    eqtr4i
    a1i
    @22
    vz
    cc
    @20
    cmpt
    wceq
    wph
    vz
    cc
    @20
    fconstmpt
    a1i
    offval2
    wph
    vz
    cc
    @29
    @10
    @26
    @26
    @28
    @29
    @10
    wceq
    wph
    @26
    id
    ftalem7.5
    @9
    cX
    subneg
    syl2anr
    mpteq2dva
    eqtrd
    wph
    vy
    cc
    cc
    cF
    wph
    cF
    cS
    cply
    cfv
    #
    wcel
    cc
    cc
    cF
    wf
    #
    ftalem.3
    cS
    cF
    plyf
    syl
    #
    feqmptd
    @8
    @10
    cF
    fveq2
    fmptco
    #
    wph
    vz
    vw
    cc
    cF
    @23
    wph
    @33
    @25
    cF
    cS
    plyssc
    ftalem.3
    sseldi
    #
    wph
    @23
    @25
    wcel
    #
    @23
    cdgr
    cfv
    #
    c1
    wceq
    #
    @23
    ccnv
    cc0
    csn
    cima
    @21
    wceq
    #
    wph
    @30
    @38
    @40
    @41
    w3a
    @31
    @20
    @23
    @23
    eqid
    plyremlem
    syl
    #
    simp1d
    #
    @26
    vw
    cv
    #
    cc
    wcel
    wa
    #
    @9
    @44
    caddc
    co
    cc
    wcel
    wph
    @9
    @44
    addcl
    adantl
    @45
    @9
    @44
    cmul
    co
    cc
    wcel
    wph
    @9
    @44
    mulcl
    adantl
    plyco
    eqeltrrd
    wph
    @24
    cdgr
    cfv
    #
    @19
    cn
    wph
    @24
    @12
    cdgr
    @36
    fveq2d
    wph
    @46
    cN
    @39
    cmul
    co
    cn
    wph
    cc
    cF
    @23
    cN
    @39
    ftalem.2
    @39
    eqid
    @37
    @43
    dgrco
    wph
    cN
    @39
    ftalem.4
    wph
    @39
    c1
    cn
    wph
    @38
    @40
    @41
    @42
    simp2d
    1nn
    syl6eqel
    nnmulcld
    eqeltrd
    eqeltrrd
    wph
    @15
    @0
    cc0
    wph
    @15
    cc0
    cX
    caddc
    co
    #
    cF
    cfv
    #
    @0
    cc0
    cc
    wcel
    @15
    @48
    wceq
    0cn
    vz
    cc0
    @11
    @48
    cc
    @12
    @9
    cc0
    wceq
    @10
    @47
    cF
    @9
    cc0
    cX
    caddc
    oveq1
    fveq2d
    @12
    eqid
    #
    @47
    cF
    fvex
    fvmpt
    ax-mp
    wph
    @47
    cX
    cF
    wph
    cX
    ftalem7.5
    addid2d
    fveq2d
    syl5eq
    #
    ftalem7.6
    eqnetrd
    ftalem6
    wph
    @17
    @7
    vy
    cc
    wph
    @8
    cc
    wcel
    #
    wa
    #
    @8
    cX
    caddc
    co
    #
    cc
    wcel
    #
    @17
    @1
    @53
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wn
    #
    @7
    @51
    @51
    @28
    @54
    wph
    @51
    id
    ftalem7.5
    @8
    cX
    addcl
    syl2anr
    #
    @52
    @17
    @58
    @52
    @17
    @56
    @1
    clt
    wbr
    @58
    @52
    @14
    @56
    @16
    @1
    clt
    @52
    @13
    @55
    cabs
    @51
    @13
    @55
    wceq
    wph
    vz
    @8
    @11
    @55
    cc
    @12
    @9
    @8
    wceq
    @10
    @53
    cF
    @9
    @8
    cX
    caddc
    oveq1
    fveq2d
    @49
    @53
    cF
    fvex
    fvmpt
    adantl
    fveq2d
    @52
    @15
    @0
    cabs
    wph
    @15
    @0
    wceq
    @51
    @50
    adantr
    fveq2d
    breq12d
    @52
    @56
    @1
    @52
    @55
    @52
    cc
    cc
    @53
    cF
    wph
    @34
    @51
    @35
    adantr
    @59
    ffvelrnd
    abscld
    wph
    @1
    cr
    wcel
    @51
    wph
    @0
    wph
    cc
    cc
    cX
    cF
    @35
    ftalem7.5
    ffvelrnd
    abscld
    adantr
    ltnled
    bitrd
    biimpd
    @6
    @58
    vx
    @53
    cc
    @2
    @53
    wceq
    #
    @5
    @57
    @60
    @4
    @56
    @1
    cle
    @60
    @3
    @55
    cabs
    @2
    @53
    cF
    fveq2
    fveq2d
    breq2d
    notbid
    rspcev
    syl6an
    rexlimdva
    mpd
    @5
    vx
    cc
    rexnal
    sylib
end
