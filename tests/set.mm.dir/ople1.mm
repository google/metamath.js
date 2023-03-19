include "cops.mm"
include "wcel.mm"
include "wa.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cdm.mm"
include "cglb.mm"
include "op01dm.mm"
include "simpld.mm"
include "adantr.mm"
include "ple1.mm"

theorem ople1
  let cB: class B
  let c.1: class .1.
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume ople1.b: |- B = ( Base ` K )
  assume ople1.l: |- .<_ = ( le ` K )
  assume ople1.u: |- .1. = ( 1. ` K )


  assert |- ( ( K e. OP /\ X e. B ) -> X .<_ .1. )

  proof
    cK
    cops
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cB
    cK
    club
    cfv
    #
    c.1
    cK
    c.le
    cops
    cX
    ople1.b
    @2
    eqid
    #
    ople1.l
    ople1.u
    @0
    @1
    simpl
    @0
    @1
    simpr
    @0
    cB
    @2
    cdm
    wcel
    #
    @1
    @0
    @4
    cB
    cK
    cglb
    cfv
    #
    cdm
    wcel
    cB
    @2
    @5
    cK
    ople1.b
    @3
    @5
    eqid
    op01dm
    simpld
    adantr
    ple1
end
