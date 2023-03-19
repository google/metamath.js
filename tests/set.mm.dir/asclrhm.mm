include "casa.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cmulr.mm"
include "cur.mm"
include "eqid.mm"
include "ccrg.mm"
include "crg.mm"
include "assasca.mm"
include "crngring.mm"
include "syl.mm"
include "assaring.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "ringidcl.mm"
include "asclval.mm"
include "3syl.mm"
include "clmod.mm"
include "assalmod.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cv.mm"
include "wa.mm"
include "ringlidm.mm"
include "adantr.mm"
include "oveq2d.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "assaass.mm"
include "syl13anc.mm"
include "assaassr.mm"
include "lmodvsass.mm"
include "3eqtr4rd.mm"
include "ringcl.mm"
include "3expb.mm"
include "sylan.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "asclghm.mm"
include "isrhm2d.mm"

theorem asclrhm
  let cA: class A
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume asclrhm.a: |- A = ( algSc ` W )
  assume asclrhm.f: |- F = ( Scalar ` W )


  assert |- ( W e. AssAlg -> A e. ( F RingHom W ) )

  proof
    cW
    casa
    wcel
    #
    vx
    vy
    cF
    cbs
    cfv
    #
    cF
    cW
    cF
    cmulr
    cfv
    #
    cW
    cmulr
    cfv
    #
    cF
    cur
    cfv
    #
    cA
    cW
    cur
    cfv
    #
    @1
    eqid
    #
    @4
    eqid
    #
    @5
    eqid
    #
    @2
    eqid
    #
    @3
    eqid
    #
    @0
    cF
    ccrg
    wcel
    cF
    crg
    wcel
    #
    cF
    cW
    asclrhm.f
    assasca
    cF
    crngring
    syl
    #
    cW
    assaring
    #
    @0
    @4
    cA
    cfv
    #
    @4
    @5
    cW
    cvsca
    cfv
    #
    co
    #
    @5
    @0
    @11
    @4
    @1
    wcel
    @14
    @16
    wceq
    @12
    @1
    cF
    @4
    @6
    @7
    ringidcl
    cA
    @15
    @5
    cF
    @1
    cW
    @4
    asclrhm.a
    asclrhm.f
    @6
    @15
    eqid
    #
    @8
    asclval
    3syl
    @0
    cW
    clmod
    wcel
    #
    @5
    cW
    cbs
    cfv
    #
    wcel
    #
    @16
    @5
    wceq
    cW
    assalmod
    #
    @0
    cW
    crg
    wcel
    #
    @20
    @13
    @19
    cW
    @5
    @19
    eqid
    #
    @8
    ringidcl
    syl
    #
    @15
    @4
    cF
    @19
    cW
    @5
    @23
    asclrhm.f
    @17
    @7
    lmodvs1
    syl2anc
    eqtrd
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    wa
    #
    @25
    @27
    @2
    co
    #
    @5
    @15
    co
    #
    @25
    @5
    @15
    co
    #
    @27
    @5
    @15
    co
    #
    @3
    co
    #
    @31
    cA
    cfv
    #
    @25
    cA
    cfv
    #
    @27
    cA
    cfv
    #
    @3
    co
    @30
    @25
    @27
    @5
    @5
    @3
    co
    #
    @15
    co
    #
    @15
    co
    #
    @25
    @34
    @15
    co
    #
    @35
    @32
    @30
    @40
    @34
    @25
    @15
    @30
    @39
    @5
    @27
    @15
    @0
    @39
    @5
    wceq
    #
    @29
    @0
    @22
    @20
    @43
    @13
    @24
    @19
    cW
    @3
    @5
    @5
    @23
    @10
    @8
    ringlidm
    syl2anc
    adantr
    oveq2d
    oveq2d
    @30
    @35
    @25
    @5
    @34
    @3
    co
    #
    @15
    co
    #
    @41
    @30
    @0
    @26
    @20
    @34
    @19
    wcel
    #
    @35
    @45
    wceq
    @0
    @29
    simpl
    #
    @0
    @26
    @28
    simprl
    #
    @0
    @20
    @29
    @24
    adantr
    #
    @30
    @18
    @28
    @20
    @46
    @0
    @18
    @29
    @21
    adantr
    #
    @0
    @26
    @28
    simprr
    #
    @49
    @27
    @15
    cF
    @1
    @19
    cW
    @5
    @23
    asclrhm.f
    @17
    @6
    lmodvscl
    syl3anc
    @25
    @1
    @15
    @3
    cF
    @19
    cW
    @5
    @34
    @23
    asclrhm.f
    @6
    @17
    @10
    assaass
    syl13anc
    @30
    @44
    @40
    @25
    @15
    @30
    @0
    @28
    @20
    @20
    @44
    @40
    wceq
    @47
    @51
    @49
    @49
    @27
    @1
    @15
    @3
    cF
    @19
    cW
    @5
    @5
    @23
    asclrhm.f
    @6
    @17
    @10
    assaassr
    syl13anc
    oveq2d
    eqtrd
    @30
    @18
    @26
    @28
    @20
    @32
    @42
    wceq
    @50
    @48
    @51
    @49
    @25
    @27
    @15
    @2
    cF
    @1
    @19
    cW
    @5
    @23
    asclrhm.f
    @17
    @6
    @9
    lmodvsass
    syl13anc
    3eqtr4rd
    @30
    @31
    @1
    wcel
    #
    @36
    @32
    wceq
    @0
    @11
    @29
    @52
    @12
    @11
    @26
    @28
    @52
    @1
    cF
    @2
    @25
    @27
    @6
    @9
    ringcl
    3expb
    sylan
    cA
    @15
    @5
    cF
    @1
    cW
    @31
    asclrhm.a
    asclrhm.f
    @6
    @17
    @8
    asclval
    syl
    @30
    @37
    @33
    @38
    @34
    @3
    @30
    @26
    @37
    @33
    wceq
    @48
    cA
    @15
    @5
    cF
    @1
    cW
    @25
    asclrhm.a
    asclrhm.f
    @6
    @17
    @8
    asclval
    syl
    @30
    @28
    @38
    @34
    wceq
    @51
    cA
    @15
    @5
    cF
    @1
    cW
    @27
    asclrhm.a
    asclrhm.f
    @6
    @17
    @8
    asclval
    syl
    oveq12d
    3eqtr4d
    @0
    cA
    cF
    cW
    asclrhm.a
    asclrhm.f
    @13
    @21
    asclghm
    isrhm2d
end
