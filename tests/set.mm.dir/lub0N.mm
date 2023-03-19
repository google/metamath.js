include "cops.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "cbs.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "biid.mm"
include "id.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "lubval.mm"
include "op0cl.mm"
include "wceq.mm"
include "ral0.mm"
include "a1bi.mm"
include "ralbii.mm"
include "biantrur.mm"
include "bitri.mm"
include "adantr.mm"
include "breq2.mm"
include "rspcv.mm"
include "syl.mm"
include "ople0.mm"
include "sylibd.mm"
include "op0le.mm"
include "adantlr.mm"
include "ex.mm"
include "breq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "com23.mm"
include "ralrimdv.mm"
include "impbid.mm"
include "syl5bbr.mm"
include "riota5.mm"
include "eqtrd.mm"

theorem lub0N
  let c.1: class .1.
  let cK: class K
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lub0.u: |- .1. = ( lub ` K )
  assume lub0.z: |- .0. = ( 0. ` K )


  assert |- ( K e. OP -> ( .1. ` (/) ) = .0. )

  proof
    cK
    cops
    wcel
    #
    c0
    c.1
    cfv
    vy
    cv
    #
    vx
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    vy
    c0
    wral
    #
    @1
    vz
    cv
    #
    @3
    wbr
    #
    vy
    c0
    wral
    #
    @2
    @6
    @3
    wbr
    #
    wi
    #
    vz
    cK
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vx
    @11
    crio
    c.0
    @0
    @13
    vx
    vy
    vz
    @11
    c0
    c.1
    cK
    @3
    cops
    @11
    eqid
    #
    @3
    eqid
    #
    lub0.u
    @13
    biid
    @0
    id
    c0
    @11
    wss
    @0
    @11
    0ss
    a1i
    lubval
    @0
    @13
    vx
    @11
    c.0
    @11
    cK
    c.0
    @14
    lub0.z
    op0cl
    #
    @13
    @9
    vz
    @11
    wral
    #
    @0
    @2
    @11
    wcel
    #
    wa
    #
    @2
    c.0
    wceq
    #
    @17
    @12
    @13
    @9
    @10
    vz
    @11
    @8
    @9
    @7
    vy
    ral0
    a1bi
    ralbii
    @5
    @12
    @4
    vy
    ral0
    biantrur
    bitri
    @19
    @17
    @20
    @19
    @17
    @2
    c.0
    @3
    wbr
    #
    @20
    @19
    c.0
    @11
    wcel
    #
    @17
    @21
    wi
    @0
    @22
    @18
    @16
    adantr
    @9
    @21
    vz
    c.0
    @11
    @6
    c.0
    @2
    @3
    breq2
    rspcv
    syl
    @11
    cK
    @3
    @2
    c.0
    @14
    @15
    lub0.z
    ople0
    sylibd
    @19
    @20
    @9
    vz
    @11
    @19
    @6
    @11
    wcel
    #
    @20
    @9
    @19
    @23
    c.0
    @6
    @3
    wbr
    #
    @20
    @9
    wi
    @19
    @23
    @24
    @0
    @23
    @24
    @18
    @11
    cK
    @3
    @6
    c.0
    @14
    @15
    lub0.z
    op0le
    adantlr
    ex
    @20
    @9
    @24
    @2
    c.0
    @6
    @3
    breq1
    biimprcd
    syl6
    com23
    ralrimdv
    impbid
    syl5bbr
    riota5
    eqtrd
end
