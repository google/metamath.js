include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "cin.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cur.mm"
include "cress.mm"
include "co.mm"
include "csra.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "subrgss.mm"
include "srabase.mm"
include "sraaddg.mm"
include "srasca.mm"
include "sravsca.mm"
include "ressbas.mm"
include "ressplusg.mm"
include "ressmulr.mm"
include "subrg1.mm"
include "subrgring.mm"
include "cgrp.mm"
include "crg.mm"
include "subrgrcl.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqidd.mm"
include "cv.mm"
include "wa.mm"
include "oveqdr.mm"
include "grppropd.mm"
include "mpbid.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "inss2.mm"
include "sseli.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr1.mm"
include "sseldi.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ringdi.mm"
include "syl13anc.mm"
include "ringdir.mm"
include "ringass.mm"
include "ringlidm.mm"
include "sylan.mm"
include "islmodd.mm"

theorem sralmod
  let cA: class A
  let cS: class S
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sralmod.a: |- A = ( ( subringAlg ` W ) ` S )


  assert |- ( S e. ( SubRing ` W ) -> A e. LMod )

  proof
    cS
    cW
    csubrg
    cfv
    #
    wcel
    #
    vx
    vy
    vz
    cS
    cW
    cbs
    cfv
    #
    cin
    #
    cW
    cplusg
    cfv
    #
    @4
    cW
    cmulr
    cfv
    #
    @5
    cW
    cur
    cfv
    #
    cW
    cS
    cress
    co
    #
    @2
    cA
    @1
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
    @1
    sralmod.a
    a1i
    #
    cS
    @2
    cW
    @2
    eqid
    #
    subrgss
    #
    srabase
    #
    @1
    cA
    cS
    cW
    @8
    @10
    sraaddg
    #
    @1
    cA
    cS
    cW
    @8
    @10
    srasca
    @1
    cA
    cS
    cW
    @8
    @10
    sravsca
    cS
    @2
    @7
    @0
    cW
    @7
    eqid
    #
    @9
    ressbas
    cS
    @4
    cW
    @7
    @0
    @13
    @4
    eqid
    #
    ressplusg
    cS
    cW
    @7
    @5
    @0
    @13
    @5
    eqid
    #
    ressmulr
    cS
    cW
    @7
    @6
    @13
    @6
    eqid
    #
    subrg1
    cS
    cW
    @7
    @13
    subrgring
    @1
    cW
    cgrp
    wcel
    #
    cA
    cgrp
    wcel
    @1
    cW
    crg
    wcel
    #
    @17
    cS
    cW
    subrgrcl
    #
    cW
    ringgrp
    syl
    @1
    vx
    vy
    @2
    cW
    cA
    @1
    @2
    eqidd
    @11
    @1
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    vx
    vy
    @4
    cA
    cplusg
    cfv
    @12
    oveqdr
    grppropd
    mpbid
    @1
    @20
    @3
    wcel
    #
    @23
    w3a
    @18
    @21
    @23
    @20
    @22
    @5
    co
    #
    @2
    wcel
    @1
    @24
    @18
    @23
    @19
    3ad2ant1
    @24
    @1
    @21
    @23
    @3
    @2
    @20
    cS
    @2
    inss2
    #
    sseli
    3ad2ant2
    @1
    @24
    @23
    simp3
    @2
    cW
    @5
    @20
    @22
    @9
    @15
    ringcl
    syl3anc
    @1
    @24
    @23
    vz
    cv
    #
    @2
    wcel
    #
    w3a
    #
    wa
    #
    @18
    @21
    @23
    @28
    @20
    @22
    @27
    @4
    co
    @5
    co
    @25
    @20
    @27
    @5
    co
    #
    @4
    co
    wceq
    @1
    @18
    @29
    @19
    adantr
    @30
    @3
    @2
    @20
    @26
    @1
    @24
    @23
    @28
    simpr1
    sseldi
    @1
    @24
    @23
    @28
    simpr2
    @1
    @24
    @23
    @28
    simpr3
    @2
    @4
    cW
    @5
    @20
    @22
    @27
    @9
    @14
    @15
    ringdi
    syl13anc
    @1
    @24
    @22
    @3
    wcel
    #
    @28
    w3a
    #
    wa
    #
    @18
    @21
    @23
    @28
    @20
    @22
    @4
    co
    @27
    @5
    co
    @31
    @22
    @27
    @5
    co
    #
    @4
    co
    wceq
    @1
    @18
    @33
    @19
    adantr
    #
    @34
    @3
    @2
    @20
    @26
    @1
    @24
    @32
    @28
    simpr1
    sseldi
    #
    @34
    @3
    @2
    @22
    @26
    @1
    @24
    @32
    @28
    simpr2
    sseldi
    #
    @1
    @24
    @32
    @28
    simpr3
    #
    @2
    @4
    cW
    @5
    @20
    @22
    @27
    @9
    @14
    @15
    ringdir
    syl13anc
    @34
    @18
    @21
    @23
    @28
    @25
    @27
    @5
    co
    @20
    @35
    @5
    co
    wceq
    @36
    @37
    @38
    @39
    @2
    cW
    @5
    @20
    @22
    @27
    @9
    @15
    ringass
    syl13anc
    @1
    @18
    @21
    @6
    @20
    @5
    co
    @20
    wceq
    @19
    @2
    cW
    @5
    @6
    @20
    @9
    @15
    @16
    ringlidm
    sylan
    islmodd
end
