include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "casa.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmnd.mm"
include "crg.mm"
include "assaring.mm"
include "ringmgp.mm"
include "syl.mm"
include "adantl.mm"
include "adantr.mm"
include "simpll.mm"
include "clmod.mm"
include "assalmod.mm"
include "simplr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mgpbas.mm"
include "eqid.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "oveq1.mm"
include "csca.mm"
include "cbs.mm"
include "simprr.mm"
include "ccrg.mm"
include "assasca.mm"
include "crngring.mm"
include "3syl.mm"
include "simpl.mm"
include "wi.mm"
include "a1i.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "imp.mm"
include "eqcomi.mm"
include "mulgnn0cl.mm"
include "simprlr.mm"
include "assaass.mm"
include "syl13anc.mm"
include "assaassr.mm"
include "oveq2d.mm"
include "eqcomd.mm"
include "peano2nn0.mm"
include "w3a.mm"
include "lmodvsass.mm"
include "3eqtrd.mm"
include "simprll.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "exp31.mm"

theorem assamulgscmlem2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  assume assamulgscm.v: |- V = ( Base ` W )
  assume assamulgscm.f: |- F = ( Scalar ` W )
  assume assamulgscm.b: |- B = ( Base ` F )
  assume assamulgscm.s: |- .x. = ( .s ` W )
  assume assamulgscm.g: |- G = ( mulGrp ` F )
  assume assamulgscm.p: |- .^ = ( .g ` G )
  assume assamulgscm.h: |- H = ( mulGrp ` W )
  assume assamulgscm.e: |- E = ( .g ` H )


  assert |- ( y e. NN0 -> ( ( ( A e. B /\ X e. V ) /\ W e. AssAlg ) -> ( ( y E ( A .x. X ) ) = ( ( y .^ A ) .x. ( y E X ) ) -> ( ( y + 1 ) E ( A .x. X ) ) = ( ( ( y + 1 ) .^ A ) .x. ( ( y + 1 ) E X ) ) ) ) )

  proof
    vy
    cv
    #
    cn0
    wcel
    #
    cA
    cB
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cW
    casa
    wcel
    #
    wa
    #
    @0
    cA
    cX
    c.x
    co
    #
    cE
    co
    #
    @0
    cA
    c.ex
    co
    #
    @0
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    #
    @0
    c1
    caddc
    co
    #
    @7
    cE
    co
    #
    @13
    cA
    c.ex
    co
    #
    @13
    cX
    cE
    co
    #
    c.x
    co
    #
    wceq
    @1
    @6
    wa
    #
    @12
    wa
    #
    @14
    @8
    @7
    cW
    cmulr
    cfv
    #
    co
    #
    @17
    @19
    cH
    cmnd
    wcel
    #
    @1
    @7
    cV
    wcel
    #
    @14
    @21
    wceq
    @18
    @22
    @12
    @6
    @22
    @1
    @5
    @22
    @4
    @5
    cW
    crg
    wcel
    @22
    cW
    assaring
    cW
    cH
    assamulgscm.h
    ringmgp
    syl
    adantl
    adantl
    #
    adantr
    @1
    @6
    @12
    simpll
    @18
    @23
    @12
    @6
    @23
    @1
    @6
    cW
    clmod
    wcel
    #
    @2
    @3
    @23
    @5
    @25
    @4
    cW
    assalmod
    adantl
    #
    @2
    @3
    @5
    simpll
    @2
    @3
    @5
    simplr
    cA
    c.x
    cF
    cB
    cV
    cW
    cX
    assamulgscm.v
    assamulgscm.f
    assamulgscm.s
    assamulgscm.b
    lmodvscl
    syl3anc
    adantl
    #
    adantr
    cV
    @20
    cE
    cH
    @0
    @7
    cV
    cW
    cH
    assamulgscm.h
    assamulgscm.v
    mgpbas
    #
    assamulgscm.e
    cW
    @20
    cH
    assamulgscm.h
    @20
    eqid
    #
    mgpplusg
    #
    mulgnn0p1
    syl3anc
    @12
    @18
    @21
    @11
    @7
    @20
    co
    #
    @17
    @8
    @11
    @7
    @20
    oveq1
    @18
    @31
    @9
    @10
    @7
    @20
    co
    #
    c.x
    co
    #
    @9
    cA
    cW
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    @16
    c.x
    co
    #
    @17
    @18
    @5
    @9
    @34
    cbs
    cfv
    #
    wcel
    #
    @10
    cV
    wcel
    #
    @23
    @31
    @33
    wceq
    @1
    @4
    @5
    simprr
    #
    @18
    cG
    cmnd
    wcel
    #
    @1
    cA
    @38
    wcel
    #
    @39
    @6
    @42
    @1
    @5
    @42
    @4
    @5
    cF
    ccrg
    wcel
    cF
    crg
    wcel
    @42
    cF
    cW
    assamulgscm.f
    assasca
    cF
    crngring
    cF
    cG
    assamulgscm.g
    ringmgp
    3syl
    adantl
    adantl
    #
    @1
    @6
    simpl
    #
    @6
    @43
    @1
    @4
    @5
    @43
    @2
    @5
    @43
    wi
    @3
    @5
    @2
    @43
    @5
    cB
    @38
    cA
    @5
    cB
    cF
    cbs
    cfv
    #
    @38
    cB
    @46
    wceq
    @5
    assamulgscm.b
    a1i
    cF
    @34
    cbs
    assamulgscm.f
    fveq2i
    syl6eq
    eleq2d
    biimpcd
    adantr
    imp
    adantl
    #
    @38
    c.ex
    cG
    @0
    cA
    @38
    cF
    cG
    assamulgscm.g
    @34
    cF
    cbs
    cF
    @34
    assamulgscm.f
    eqcomi
    fveq2i
    mgpbas
    assamulgscm.p
    mulgnn0cl
    syl3anc
    #
    @18
    @22
    @1
    @3
    @40
    @24
    @45
    @1
    @2
    @3
    @5
    simprlr
    #
    cV
    cE
    cH
    @0
    cX
    @28
    assamulgscm.e
    mulgnn0cl
    syl3anc
    #
    @27
    @9
    @38
    c.x
    @20
    @34
    cV
    cW
    @10
    @7
    assamulgscm.v
    @34
    eqid
    #
    @38
    eqid
    #
    assamulgscm.s
    @29
    assaass
    syl13anc
    @18
    @33
    @9
    cA
    @10
    cX
    @20
    co
    #
    c.x
    co
    #
    c.x
    co
    @9
    cA
    @16
    c.x
    co
    #
    c.x
    co
    #
    @37
    @18
    @32
    @54
    @9
    c.x
    @18
    @5
    @43
    @40
    @3
    @32
    @54
    wceq
    @41
    @47
    @50
    @49
    cA
    @38
    c.x
    @20
    @34
    cV
    cW
    @10
    cX
    assamulgscm.v
    @51
    @52
    assamulgscm.s
    @29
    assaassr
    syl13anc
    oveq2d
    @18
    @54
    @55
    @9
    c.x
    @18
    @53
    @16
    cA
    c.x
    @18
    @16
    @53
    @18
    @22
    @1
    @3
    @16
    @53
    wceq
    @24
    @45
    @49
    cV
    @20
    cE
    cH
    @0
    cX
    @28
    assamulgscm.e
    @30
    mulgnn0p1
    syl3anc
    eqcomd
    oveq2d
    oveq2d
    @18
    @25
    @39
    @43
    @16
    cV
    wcel
    #
    @56
    @37
    wceq
    @6
    @25
    @1
    @26
    adantl
    @48
    @47
    @18
    @22
    @13
    cn0
    wcel
    #
    @3
    @57
    @24
    @1
    @58
    @6
    @0
    peano2nn0
    adantr
    @49
    cV
    cE
    cH
    @13
    cX
    @28
    assamulgscm.e
    mulgnn0cl
    syl3anc
    @25
    @39
    @43
    @57
    w3a
    wa
    @37
    @56
    @9
    cA
    c.x
    @35
    @34
    @38
    cV
    cW
    @16
    assamulgscm.v
    @51
    assamulgscm.s
    @52
    @35
    eqid
    lmodvsass
    eqcomd
    syl13anc
    3eqtrd
    @18
    @36
    @15
    @16
    c.x
    @18
    @15
    @36
    @18
    @15
    @9
    cA
    cF
    cmulr
    cfv
    #
    co
    #
    @36
    @18
    @42
    @1
    @2
    @15
    @60
    wceq
    @44
    @45
    @1
    @2
    @3
    @5
    simprll
    cB
    @59
    c.ex
    cG
    @0
    cA
    cB
    cF
    cG
    assamulgscm.g
    assamulgscm.b
    mgpbas
    assamulgscm.p
    cF
    @59
    cG
    assamulgscm.g
    @59
    eqid
    mgpplusg
    mulgnn0p1
    syl3anc
    @18
    @59
    @35
    @9
    cA
    @18
    cF
    @34
    cmulr
    cF
    @34
    wceq
    @18
    assamulgscm.f
    a1i
    fveq2d
    oveqd
    eqtrd
    eqcomd
    oveq1d
    3eqtrd
    sylan9eqr
    eqtrd
    exp31
end
