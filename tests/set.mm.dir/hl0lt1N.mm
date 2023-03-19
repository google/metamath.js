include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wrex.mm"
include "eqid.mm"
include "hlhgt2.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "adantr.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "syl.mm"
include "simpr.mm"
include "op1cl.mm"
include "plttr.mm"
include "syl13anc.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem hl0lt1N
  let c.lt: class .<
  let c.1: class .1.
  let cK: class K
  let c.0: class .0.
  let vx: setvar x
  assume hl0lt1.s: |- .< = ( lt ` K )
  assume hl0lt1.z: |- .0. = ( 0. ` K )
  assume hl0lt1.u: |- .1. = ( 1. ` K )


  assert |- ( K e. HL -> .0. .< .1. )

  proof
    cK
    chlt
    wcel
    #
    c.0
    vx
    cv
    #
    c.lt
    wbr
    @1
    c.1
    c.lt
    wbr
    wa
    #
    vx
    cK
    cbs
    cfv
    #
    wrex
    c.0
    c.1
    c.lt
    wbr
    #
    vx
    @3
    c.lt
    c.1
    cK
    c.0
    @3
    eqid
    #
    hl0lt1.s
    hl0lt1.z
    hl0lt1.u
    hlhgt2
    @0
    @2
    @4
    vx
    @3
    @0
    @1
    @3
    wcel
    #
    wa
    #
    cK
    cpo
    wcel
    #
    c.0
    @3
    wcel
    #
    @6
    c.1
    @3
    wcel
    #
    @2
    @4
    wi
    @0
    @8
    @6
    cK
    hlpos
    adantr
    @7
    cK
    cops
    wcel
    #
    @9
    @0
    @11
    @6
    cK
    hlop
    adantr
    #
    @3
    cK
    c.0
    @5
    hl0lt1.z
    op0cl
    syl
    @0
    @6
    simpr
    @7
    @11
    @10
    @12
    @3
    c.1
    cK
    @5
    hl0lt1.u
    op1cl
    syl
    @3
    c.lt
    cK
    c.0
    @1
    c.1
    @5
    hl0lt1.s
    plttr
    syl13anc
    rexlimdva
    mpd
end
