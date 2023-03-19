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
include "glbval.mm"
include "op1cl.mm"
include "wceq.mm"
include "ral0.mm"
include "a1bi.mm"
include "ralbii.mm"
include "biantrur.mm"
include "bitri.mm"
include "adantr.mm"
include "breq1.mm"
include "rspcv.mm"
include "syl.mm"
include "op1le.mm"
include "sylibd.mm"
include "ople1.mm"
include "adantlr.mm"
include "ex.mm"
include "breq2.mm"
include "biimprcd.mm"
include "syl6.mm"
include "com23.mm"
include "ralrimdv.mm"
include "impbid.mm"
include "syl5bbr.mm"
include "riota5.mm"
include "eqtrd.mm"

theorem glb0N
  let c.1: class .1.
  let cG: class G
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume glb0.g: |- G = ( glb ` K )
  assume glb0.u: |- .1. = ( 1. ` K )


  assert |- ( K e. OP -> ( G ` (/) ) = .1. )

  proof
    cK
    cops
    wcel
    #
    c0
    cG
    cfv
    vx
    cv
    #
    vy
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
    vz
    cv
    #
    @2
    @3
    wbr
    #
    vy
    c0
    wral
    #
    @6
    @1
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
    c.1
    @0
    @13
    vx
    vy
    vz
    @11
    c0
    cG
    cK
    @3
    cops
    @11
    eqid
    #
    @3
    eqid
    #
    glb0.g
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
    glbval
    @0
    @13
    vx
    @11
    c.1
    @11
    c.1
    cK
    @14
    glb0.u
    op1cl
    #
    @13
    @9
    vz
    @11
    wral
    #
    @0
    @1
    @11
    wcel
    #
    wa
    #
    @1
    c.1
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
    c.1
    @1
    @3
    wbr
    #
    @20
    @19
    c.1
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
    c.1
    @11
    @6
    c.1
    @1
    @3
    breq1
    rspcv
    syl
    @11
    c.1
    cK
    @3
    @1
    @14
    @15
    glb0.u
    op1le
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
    @6
    c.1
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
    c.1
    cK
    @3
    @6
    @14
    @15
    glb0.u
    ople1
    adantlr
    ex
    @20
    @9
    @24
    @1
    c.1
    @6
    @3
    breq2
    biimprcd
    syl6
    com23
    ralrimdv
    impbid
    syl5bbr
    riota5
    eqtrd
end
