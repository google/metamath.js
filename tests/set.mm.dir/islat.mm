include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cxp.mm"
include "wceq.mm"
include "cmee.mm"
include "wa.mm"
include "cpo.mm"
include "clat.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "sqxpeqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "df-lat.mm"
include "elrab2.mm"

theorem islat
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let vl: setvar l
  assume islat.b: |- B = ( Base ` K )
  assume islat.j: |- .\/ = ( join ` K )
  assume islat.m: |- ./\ = ( meet ` K )


  assert |- ( K e. Lat <-> ( K e. Poset /\ ( dom .\/ = ( B X. B ) /\ dom ./\ = ( B X. B ) ) ) )

  proof
    vl
    cv
    #
    cjn
    cfv
    #
    cdm
    #
    @0
    cbs
    cfv
    #
    @3
    cxp
    #
    wceq
    #
    @0
    cmee
    cfv
    #
    cdm
    #
    @4
    wceq
    #
    wa
    c.or
    cdm
    #
    cB
    cB
    cxp
    #
    wceq
    #
    c.an
    cdm
    #
    @10
    wceq
    #
    wa
    vl
    cK
    cpo
    clat
    @0
    cK
    wceq
    #
    @5
    @11
    @8
    @13
    @14
    @2
    @9
    @4
    @10
    @14
    @1
    c.or
    @14
    @1
    cK
    cjn
    cfv
    c.or
    @0
    cK
    cjn
    fveq2
    islat.j
    syl6eqr
    dmeqd
    @14
    @3
    cB
    @14
    @3
    cK
    cbs
    cfv
    cB
    @0
    cK
    cbs
    fveq2
    islat.b
    syl6eqr
    sqxpeqd
    #
    eqeq12d
    @14
    @7
    @12
    @4
    @10
    @14
    @6
    c.an
    @14
    @6
    cK
    cmee
    cfv
    c.an
    @0
    cK
    cmee
    fveq2
    islat.m
    syl6eqr
    dmeqd
    @15
    eqeq12d
    anbi12d
    vl
    df-lat
    elrab2
end
