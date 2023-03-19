include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "eqid.mm"
include "lssss.mm"
include "adantl.mm"
include "lssn0.mm"
include "lssvacl.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "lssvnegcl.mm"
include "3expa.mm"
include "jca.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "lmodgrp.mm"
include "adantr.mm"
include "issubg2.mm"
include "syl.mm"
include "mpbir3and.mm"

theorem lsssubg
  let cS: class S
  let cU: class U
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume lsssubg.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ U e. S ) -> U e. ( SubGrp ` W ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cU
    cW
    csubg
    cfv
    wcel
    #
    cU
    cW
    cbs
    cfv
    #
    wss
    #
    cU
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    cU
    wcel
    #
    vy
    cU
    wral
    #
    @7
    cW
    cminusg
    cfv
    #
    cfv
    cU
    wcel
    #
    wa
    #
    vx
    cU
    wral
    #
    @1
    @5
    @0
    cS
    cU
    @4
    cW
    @4
    eqid
    #
    lsssubg.s
    lssss
    adantl
    @1
    @6
    @0
    cS
    cU
    cW
    lsssubg.s
    lssn0
    adantl
    @2
    @14
    vx
    cU
    @2
    @7
    cU
    wcel
    #
    wa
    #
    @11
    @13
    @18
    @10
    vy
    cU
    @2
    @17
    @8
    cU
    wcel
    @10
    @9
    cS
    cU
    cW
    @7
    @8
    @9
    eqid
    #
    lsssubg.s
    lssvacl
    anassrs
    ralrimiva
    @0
    @1
    @17
    @13
    cS
    cU
    @12
    cW
    @7
    lsssubg.s
    @12
    eqid
    #
    lssvnegcl
    3expa
    jca
    ralrimiva
    @2
    cW
    cgrp
    wcel
    #
    @3
    @5
    @6
    @15
    w3a
    wb
    @0
    @21
    @1
    cW
    lmodgrp
    adantr
    vx
    vy
    @4
    @9
    cU
    cW
    @12
    @16
    @19
    @20
    issubg2
    syl
    mpbir3and
end
