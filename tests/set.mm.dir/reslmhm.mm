include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "cres.mm"
include "cghm.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "cbs.mm"
include "wral.mm"
include "w3a.mm"
include "lmhmlmod1.mm"
include "lsslmod.mm"
include "sylan.mm"
include "lmhmlmod2.mm"
include "adantr.mm"
include "jca.mm"
include "csubg.mm"
include "lmghm.mm"
include "lsssubg.mm"
include "resghm.mm"
include "syl2anc.mm"
include "eqid.mm"
include "lmhmsca.mm"
include "resssca.mm"
include "sylan9eq.mm"
include "simpll.mm"
include "simprl.mm"
include "wss.mm"
include "lssss.mm"
include "adantl.mm"
include "ressbas2.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrl.mm"
include "sseldd.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "simplr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "fvres.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "fveq2d.mm"
include "ressvsca.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "3jca.mm"
include "islmhm.mm"
include "sylanbrc.mm"

theorem reslmhm
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume reslmhm.u: |- U = ( LSubSp ` S )
  assume reslmhm.r: |- R = ( S |`s X )


  assert |- ( ( F e. ( S LMHom T ) /\ X e. U ) -> ( F |` X ) e. ( R LMHom T ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    #
    cR
    clmod
    wcel
    #
    cT
    clmod
    wcel
    #
    wa
    cF
    cX
    cres
    #
    cR
    cT
    cghm
    co
    wcel
    #
    cT
    csca
    cfv
    #
    cR
    csca
    cfv
    #
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    cvsca
    cfv
    #
    co
    #
    @5
    cfv
    #
    @10
    @11
    @5
    cfv
    #
    cT
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vb
    cR
    cbs
    cfv
    #
    wral
    #
    va
    @8
    cbs
    cfv
    #
    wral
    #
    w3a
    @5
    cR
    cT
    clmhm
    co
    wcel
    @2
    @3
    @4
    @0
    cS
    clmod
    wcel
    #
    @1
    @3
    cS
    cT
    cF
    lmhmlmod1
    #
    cU
    cX
    cS
    cR
    reslmhm.r
    reslmhm.u
    lsslmod
    sylan
    @0
    @4
    @1
    cS
    cT
    cF
    lmhmlmod2
    adantr
    jca
    @2
    @6
    @9
    @22
    @2
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cS
    csubg
    cfv
    wcel
    #
    @6
    @0
    @25
    @1
    cS
    cT
    cF
    lmghm
    adantr
    @0
    @23
    @1
    @26
    @24
    cU
    cX
    cS
    reslmhm.u
    lsssubg
    sylan
    cS
    cT
    cR
    cF
    cX
    reslmhm.r
    resghm
    syl2anc
    @0
    @1
    @7
    cS
    csca
    cfv
    #
    @8
    cS
    cT
    cF
    @27
    @7
    @27
    eqid
    #
    @7
    eqid
    #
    lmhmsca
    cX
    @27
    cS
    cR
    cU
    reslmhm.r
    @28
    resssca
    #
    sylan9eq
    @2
    @10
    @11
    cS
    cvsca
    cfv
    #
    co
    #
    @5
    cfv
    #
    @17
    wceq
    #
    vb
    @19
    wral
    #
    va
    @27
    cbs
    cfv
    #
    wral
    @22
    @2
    @34
    va
    vb
    @36
    @19
    @2
    @10
    @36
    wcel
    #
    @11
    @19
    wcel
    #
    wa
    #
    wa
    #
    @32
    cF
    cfv
    #
    @10
    @11
    cF
    cfv
    #
    @16
    co
    #
    @33
    @17
    @40
    @0
    @37
    @11
    cS
    cbs
    cfv
    #
    wcel
    @41
    @43
    wceq
    @0
    @1
    @39
    simpll
    @2
    @37
    @38
    simprl
    #
    @40
    cX
    @44
    @11
    @2
    cX
    @44
    wss
    #
    @39
    @1
    @46
    @0
    cU
    cX
    @44
    cS
    @44
    eqid
    #
    reslmhm.u
    lssss
    adantl
    #
    adantr
    @2
    @38
    @11
    cX
    wcel
    #
    @37
    @2
    @49
    @38
    @2
    cX
    @19
    @11
    @2
    @46
    cX
    @19
    wceq
    @48
    cX
    @44
    cR
    cS
    reslmhm.r
    @47
    ressbas2
    syl
    eleq2d
    biimpar
    adantrl
    #
    sseldd
    @36
    cS
    cT
    @31
    @16
    @44
    cF
    @27
    @10
    @11
    @28
    @36
    eqid
    #
    @47
    @31
    eqid
    #
    @16
    eqid
    #
    lmhmlin
    syl3anc
    @40
    @32
    cX
    wcel
    #
    @33
    @41
    wceq
    @40
    @23
    @1
    @37
    @49
    @54
    @2
    @23
    @39
    @0
    @23
    @1
    @24
    adantr
    adantr
    @0
    @1
    @39
    simplr
    @45
    @50
    @36
    cU
    @31
    cX
    @27
    cS
    @10
    @11
    @28
    @52
    @51
    reslmhm.u
    lssvscl
    syl22anc
    @32
    cX
    cF
    fvres
    syl
    @40
    @49
    @17
    @43
    wceq
    @50
    @49
    @15
    @42
    @10
    @16
    @11
    cX
    cF
    fvres
    oveq2d
    syl
    3eqtr4d
    ralrimivva
    @2
    @35
    @20
    va
    @36
    @21
    @2
    @27
    @8
    cbs
    @1
    @27
    @8
    wceq
    @0
    @30
    adantl
    fveq2d
    @2
    @34
    @18
    vb
    @19
    @2
    @33
    @14
    @17
    @2
    @32
    @13
    @5
    @2
    @31
    @12
    @10
    @11
    @1
    @31
    @12
    wceq
    @0
    cX
    @31
    cS
    cR
    cU
    reslmhm.r
    @52
    ressvsca
    adantl
    oveqd
    fveq2d
    eqeq1d
    ralbidv
    raleqbidv
    mpbid
    3jca
    va
    vb
    @21
    cR
    cT
    @12
    @16
    @19
    @5
    @8
    @7
    @8
    eqid
    @29
    @21
    eqid
    @19
    eqid
    @12
    eqid
    @53
    islmhm
    sylanbrc
end
