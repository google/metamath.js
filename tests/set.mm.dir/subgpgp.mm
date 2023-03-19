include "cpgp.mm"
include "wbr.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cprime.mm"
include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "cv.mm"
include "cod.mm"
include "cexp.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cbs.mm"
include "wral.mm"
include "pgpprm.mm"
include "adantr.mm"
include "eqid.mm"
include "subggrp.mm"
include "adantl.mm"
include "ispgp.mm"
include "simp3bi.mm"
include "wss.mm"
include "wi.mm"
include "subgss.mm"
include "ssralv.mm"
include "syl.mm"
include "subgod.mm"
include "adantll.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "ralbidva.mm"
include "sylibd.mm"
include "mpd.mm"
include "subgbas.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "syl3anbrc.mm"

theorem subgpgp
  let cP: class P
  let cS: class S
  let cG: class G
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( P pGrp G /\ S e. ( SubGrp ` G ) ) -> P pGrp ( G |`s S ) )

  proof
    cP
    cG
    cpgp
    wbr
    #
    cS
    cG
    csubg
    cfv
    wcel
    #
    wa
    #
    cP
    cprime
    wcel
    #
    cG
    cS
    cress
    co
    #
    cgrp
    wcel
    #
    vx
    cv
    #
    @4
    cod
    cfv
    #
    cfv
    #
    cP
    vn
    cv
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    vx
    @4
    cbs
    cfv
    #
    wral
    #
    cP
    @4
    cpgp
    wbr
    @0
    @3
    @1
    cP
    cG
    pgpprm
    adantr
    @1
    @5
    @0
    cS
    cG
    @4
    @4
    eqid
    #
    subggrp
    adantl
    @2
    @11
    vx
    cS
    wral
    #
    @13
    @2
    @6
    cG
    cod
    cfv
    #
    cfv
    #
    @9
    wceq
    #
    vn
    cn0
    wrex
    #
    vx
    cG
    cbs
    cfv
    #
    wral
    #
    @15
    @0
    @21
    @1
    @0
    @3
    cG
    cgrp
    wcel
    @21
    vx
    cP
    vn
    cG
    @16
    @20
    @20
    eqid
    #
    @16
    eqid
    #
    ispgp
    simp3bi
    adantr
    @2
    @21
    @19
    vx
    cS
    wral
    #
    @15
    @2
    cS
    @20
    wss
    #
    @21
    @24
    wi
    @1
    @25
    @0
    @20
    cS
    cG
    @22
    subgss
    adantl
    @19
    vx
    cS
    @20
    ssralv
    syl
    @2
    @19
    @11
    vx
    cS
    @2
    @6
    cS
    wcel
    #
    wa
    #
    @18
    @10
    vn
    cn0
    @27
    @17
    @8
    @9
    @1
    @26
    @17
    @8
    wceq
    @0
    @6
    @7
    cG
    @4
    @16
    cS
    @14
    @23
    @7
    eqid
    #
    subgod
    adantll
    eqeq1d
    rexbidv
    ralbidva
    sylibd
    mpd
    @2
    @11
    vx
    cS
    @12
    @1
    cS
    @12
    wceq
    @0
    cS
    cG
    @4
    @14
    subgbas
    adantl
    raleqdv
    mpbid
    vx
    cP
    vn
    @4
    @7
    @12
    @12
    eqid
    @28
    ispgp
    syl3anbrc
end
