include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c0g.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "ccom.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "cprds.mm"
include "co.mm"
include "cbs.mm"
include "crab.mm"
include "cdsmm.mm"
include "wceq.mm"
include "wfn.mm"
include "cvv.mm"
include "fvex.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "dsmmbas2.mm"
include "mpan.mm"
include "adantl.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "csupp.mm"
include "wne.mm"
include "fvco2.mm"
include "fvconst2.mm"
include "fveq2d.mm"
include "rlm0.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "neeq2d.mm"
include "rabbidva.mm"
include "elmapfn.mm"
include "crn.mm"
include "wss.mm"
include "fn0g.mm"
include "ssv.mm"
include "fnco.mm"
include "mp3an.mm"
include "fndmdif.mm"
include "sylancl.mm"
include "simplr.mm"
include "eqeltri.mm"
include "a1i.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "eleq1d.mm"
include "wfun.mm"
include "w3a.mm"
include "wb.mm"
include "elmapfun.mm"
include "id.mm"
include "3jca.mm"
include "funisfsupp.mm"
include "syl.mm"
include "bitr4d.mm"
include "cpws.mm"
include "rlmbas.mm"
include "pwsbas.mm"
include "csca.mm"
include "pwsval.mm"
include "rlmsca.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "rabeq.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "frlmval.mm"

theorem frlmbas
  let cB: class B
  let cR: class R
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmbas.n: |- N = ( Base ` R )
  assume frlmbas.z: |- .0. = ( 0g ` R )
  assume frlmbas.b: |- B = { k e. ( N ^m I ) | k finSupp .0. }

  disjoint N k
  disjoint R k
  disjoint I k
  disjoint W k
  disjoint V k
  disjoint .0. k
  disjoint N x
  disjoint k x
  disjoint R x
  disjoint B x
  disjoint I x
  disjoint W x
  disjoint V x
  disjoint .0. x
  disjoint R r
  disjoint R i
  disjoint i r
  disjoint I r
  disjoint I i
  disjoint W r
  disjoint W i
  assert |- ( ( R e. V /\ I e. W ) -> B = ( Base ` F ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    vk
    cv
    #
    c0g
    cI
    cR
    crglmod
    cfv
    #
    csn
    cxp
    #
    ccom
    #
    cdif
    cdm
    #
    cfn
    wcel
    #
    vk
    cR
    @5
    cprds
    co
    #
    cbs
    cfv
    #
    crab
    #
    cR
    @5
    cdsmm
    co
    #
    cbs
    cfv
    #
    cB
    cF
    cbs
    cfv
    @1
    @11
    @13
    wceq
    #
    @0
    @5
    cI
    wfn
    #
    @1
    @14
    @4
    cvv
    wcel
    #
    @15
    cR
    crglmod
    fvex
    #
    cI
    @4
    cvv
    fnconstg
    ax-mp
    #
    @11
    @9
    @5
    cR
    vk
    cI
    cW
    @9
    eqid
    @11
    eqid
    dsmmbas2
    mpan
    adantl
    @2
    cB
    @3
    c.0
    cfsupp
    wbr
    #
    vk
    cN
    cI
    cmap
    co
    #
    crab
    #
    @11
    frlmbas.b
    @2
    @8
    vk
    @20
    crab
    #
    @21
    @11
    @2
    @8
    @19
    vk
    @20
    @2
    @3
    @20
    wcel
    #
    wa
    #
    @8
    @3
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @19
    @24
    @7
    @25
    cfn
    @24
    vx
    cv
    #
    @3
    cfv
    #
    @27
    @6
    cfv
    #
    wne
    #
    vx
    cI
    crab
    #
    @28
    c.0
    wne
    #
    vx
    cI
    crab
    #
    @7
    @25
    @24
    @30
    @32
    vx
    cI
    @24
    @27
    cI
    wcel
    #
    wa
    #
    @29
    c.0
    @28
    @35
    @29
    @27
    @5
    cfv
    #
    c0g
    cfv
    #
    c.0
    @34
    @29
    @37
    wceq
    #
    @24
    @15
    @34
    @38
    @18
    cI
    c0g
    @5
    @27
    fvco2
    mpan
    adantl
    @35
    @37
    @4
    c0g
    cfv
    #
    c.0
    @35
    @36
    @4
    c0g
    @34
    @36
    @4
    wceq
    @24
    cI
    @4
    @27
    @17
    fvconst2
    adantl
    fveq2d
    c.0
    cR
    c0g
    cfv
    #
    @39
    frlmbas.z
    cR
    rlm0
    eqtri
    syl6eqr
    eqtrd
    neeq2d
    rabbidva
    @24
    @3
    cI
    wfn
    #
    @6
    cI
    wfn
    #
    @7
    @31
    wceq
    @23
    @41
    @2
    @3
    cN
    cI
    elmapfn
    adantl
    #
    c0g
    cvv
    wfn
    @15
    @5
    crn
    #
    cvv
    wss
    @42
    fn0g
    @18
    @44
    ssv
    cvv
    cI
    c0g
    @5
    fnco
    mp3an
    vx
    cI
    @3
    @6
    fndmdif
    sylancl
    @24
    @41
    @1
    c.0
    cvv
    wcel
    #
    @25
    @33
    wceq
    @43
    @0
    @1
    @23
    simplr
    @45
    @24
    c.0
    @40
    cvv
    frlmbas.z
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    vx
    @3
    cW
    cvv
    cI
    c.0
    suppvalfn
    syl3anc
    3eqtr4d
    eleq1d
    @24
    @3
    wfun
    #
    @23
    @45
    w3a
    #
    @19
    @26
    wb
    @23
    @48
    @2
    @23
    @47
    @23
    @45
    @3
    cN
    cI
    elmapfun
    @23
    id
    @45
    @23
    @46
    a1i
    3jca
    adantl
    @3
    @20
    cvv
    c.0
    funisfsupp
    syl
    bitr4d
    rabbidva
    @2
    @20
    @10
    wceq
    @22
    @11
    wceq
    @2
    @20
    @4
    cI
    cpws
    co
    #
    cbs
    cfv
    #
    @10
    @1
    @20
    @50
    wceq
    #
    @0
    @16
    @1
    @51
    @17
    cN
    @4
    cI
    cvv
    cW
    @49
    @49
    eqid
    #
    cN
    cR
    cbs
    cfv
    @4
    cbs
    cfv
    frlmbas.n
    cR
    rlmbas
    eqtri
    pwsbas
    mpan
    adantl
    @2
    @49
    @9
    cbs
    @2
    @49
    @4
    csca
    cfv
    #
    @5
    cprds
    co
    #
    @9
    @1
    @49
    @54
    wceq
    #
    @0
    @16
    @1
    @55
    @17
    @4
    @53
    cI
    cvv
    cW
    @49
    @52
    @53
    eqid
    pwsval
    mpan
    adantl
    @2
    cR
    @53
    @5
    cprds
    @0
    cR
    @53
    wceq
    @1
    cR
    cV
    rlmsca
    adantr
    oveq1d
    eqtr4d
    fveq2d
    eqtrd
    @8
    vk
    @20
    @10
    rabeq
    syl
    eqtr3d
    syl5eq
    @2
    cF
    @12
    cbs
    cR
    cF
    cI
    cV
    cW
    frlmval.f
    frlmval
    fveq2d
    3eqtr4d
end
