include "ccrg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cmulr.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "csra.mm"
include "wceq.mm"
include "a1i.mm"
include "wss.mm"
include "eqid.mm"
include "subrgss.mm"
include "adantl.mm"
include "srabase.mm"
include "srasca.mm"
include "subrgbas.mm"
include "sravsca.mm"
include "sramulr.mm"
include "clmod.mm"
include "sralmod.mm"
include "crg.mm"
include "crngring.mm"
include "adantr.mm"
include "eqidd.mm"
include "cv.mm"
include "cplusg.mm"
include "sraaddg.mm"
include "oveqdr.mm"
include "ringpropd.mm"
include "mpbid.mm"
include "subrgcrng.mm"
include "w3a.mm"
include "simpr1.mm"
include "sseldd.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ringass.mm"
include "syl13anc.mm"
include "cmgp.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "ad2antrr.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cmn12.mm"
include "isassad.mm"

theorem sraassa
  let cA: class A
  let cS: class S
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sraassa.a: |- A = ( ( subringAlg ` W ) ` S )


  assert |- ( ( W e. CRing /\ S e. ( SubRing ` W ) ) -> A e. AssAlg )

  proof
    cW
    ccrg
    wcel
    #
    cS
    cW
    csubrg
    cfv
    wcel
    #
    wa
    #
    vy
    vz
    cS
    cW
    cmulr
    cfv
    #
    @3
    cW
    cS
    cress
    co
    #
    cW
    cbs
    cfv
    #
    cA
    vx
    @2
    cA
    cS
    cW
    cA
    cS
    cW
    csra
    cfv
    cfv
    wceq
    @2
    sraassa.a
    a1i
    #
    @1
    cS
    @5
    wss
    #
    @0
    cS
    @5
    cW
    @5
    eqid
    #
    subrgss
    adantl
    #
    srabase
    #
    @2
    cA
    cS
    cW
    @6
    @9
    srasca
    @1
    cS
    @4
    cbs
    cfv
    wceq
    @0
    cS
    cW
    @4
    @4
    eqid
    #
    subrgbas
    adantl
    @2
    cA
    cS
    cW
    @6
    @9
    sravsca
    @2
    cA
    cS
    cW
    @6
    @9
    sramulr
    #
    @1
    cA
    clmod
    wcel
    @0
    cA
    cS
    cW
    sraassa.a
    sralmod
    adantl
    @2
    cW
    crg
    wcel
    #
    cA
    crg
    wcel
    @0
    @13
    @1
    cW
    crngring
    adantr
    #
    @2
    vx
    vy
    @5
    cW
    cA
    @2
    @5
    eqidd
    @10
    @2
    vx
    cv
    #
    @5
    wcel
    #
    vy
    cv
    #
    @5
    wcel
    #
    wa
    #
    vx
    vy
    cW
    cplusg
    cfv
    cA
    cplusg
    cfv
    @2
    cA
    cS
    cW
    @6
    @9
    sraaddg
    oveqdr
    @2
    @19
    vx
    vy
    @3
    cA
    cmulr
    cfv
    @12
    oveqdr
    ringpropd
    mpbid
    cS
    cW
    @4
    @11
    subrgcrng
    @2
    @15
    cS
    wcel
    #
    @18
    vz
    cv
    #
    @5
    wcel
    #
    w3a
    #
    wa
    #
    @13
    @16
    @18
    @22
    @15
    @17
    @3
    co
    @21
    @3
    co
    @15
    @17
    @21
    @3
    co
    @3
    co
    #
    wceq
    @2
    @13
    @23
    @14
    adantr
    @24
    cS
    @5
    @15
    @2
    @7
    @23
    @9
    adantr
    @2
    @20
    @18
    @22
    simpr1
    sseldd
    #
    @2
    @20
    @18
    @22
    simpr2
    #
    @2
    @20
    @18
    @22
    simpr3
    #
    @5
    cW
    @3
    @15
    @17
    @21
    @8
    @3
    eqid
    #
    ringass
    syl13anc
    @24
    cW
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    @18
    @16
    @22
    @17
    @15
    @21
    @3
    co
    @3
    co
    @25
    wceq
    @0
    @31
    @1
    @23
    cW
    @30
    @30
    eqid
    #
    crngmgp
    ad2antrr
    @27
    @26
    @28
    @5
    @3
    @30
    @17
    @15
    @21
    @5
    cW
    @30
    @32
    @8
    mgpbas
    cW
    @3
    @30
    @32
    @29
    mgpplusg
    cmn12
    syl13anc
    isassad
end
