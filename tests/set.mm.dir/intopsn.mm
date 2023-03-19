include "cxp.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "cop.mm"
include "simpl.mm"
include "id.mm"
include "sqxpeqd.mm"
include "feq23d.mm"
include "syl5ibcom.mm"
include "cdm.mm"
include "fdm.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "xpid11.mm"
include "syl6ib.mm"
include "impbid.mm"
include "simpr.mm"
include "xpsng.mm"
include "sylancom.mm"
include "feq2d.mm"
include "wb.mm"
include "cvv.mm"
include "opex.mm"
include "fsng.mm"
include "mpan.mm"
include "adantl.mm"
include "3bitrd.mm"

theorem intopsn
  let cB: class B
  let c.op: class .o.
  let cZ: class Z


  assert |- ( ( .o. : ( B X. B ) --> B /\ Z e. B ) -> ( B = { Z } <-> .o. = { <. <. Z , Z >. , Z >. } ) )

  proof
    cB
    cB
    cxp
    #
    cB
    c.op
    wf
    #
    cZ
    cB
    wcel
    #
    wa
    #
    cB
    cZ
    csn
    #
    wceq
    #
    @4
    @4
    cxp
    #
    @4
    c.op
    wf
    #
    cZ
    cZ
    cop
    #
    csn
    #
    @4
    c.op
    wf
    #
    c.op
    @8
    cZ
    cop
    csn
    wceq
    #
    @3
    @5
    @7
    @3
    @1
    @5
    @7
    @1
    @2
    simpl
    @5
    @0
    cB
    @6
    @4
    c.op
    @5
    cB
    @4
    @5
    id
    #
    sqxpeqd
    @12
    feq23d
    syl5ibcom
    @3
    @7
    @0
    @6
    wceq
    #
    @5
    @3
    @0
    c.op
    cdm
    #
    wceq
    #
    @7
    @13
    @1
    @15
    @2
    @1
    @14
    @0
    @0
    cB
    c.op
    fdm
    eqcomd
    adantr
    @7
    @14
    @6
    @0
    @6
    @4
    c.op
    fdm
    eqeq2d
    syl5ibcom
    cB
    @4
    xpid11
    syl6ib
    impbid
    @3
    @6
    @9
    @4
    c.op
    @1
    @2
    @2
    @6
    @9
    wceq
    @1
    @2
    simpr
    cZ
    cZ
    cB
    cB
    xpsng
    sylancom
    feq2d
    @2
    @10
    @11
    wb
    #
    @1
    @8
    cvv
    wcel
    @2
    @16
    cZ
    cZ
    opex
    @8
    cZ
    cvv
    cB
    c.op
    fsng
    mpan
    adantl
    3bitrd
end
