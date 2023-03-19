include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "eqid.mm"
include "islpidl.mm"
include "wa.mm"
include "wss.mm"
include "snssi.mm"
include "rspcl.mm"
include "sylan2.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem lpiss
  let cP: class P
  let cR: class R
  let cU: class U
  let vr: setvar r
  let va: setvar a
  let vg: setvar g
  let cB: class B
  let cK: class K
  let cI: class I
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpiss.u: |- U = ( LIdeal ` R )


  assert |- ( R e. Ring -> P C_ U )

  proof
    cR
    crg
    wcel
    #
    va
    cP
    cU
    @0
    va
    cv
    #
    cP
    wcel
    @1
    vg
    cv
    #
    csn
    #
    cR
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vg
    cR
    cbs
    cfv
    #
    wrex
    @1
    cU
    wcel
    #
    @7
    cP
    cR
    vg
    @1
    @4
    lpival.p
    @4
    eqid
    #
    @7
    eqid
    #
    islpidl
    @0
    @6
    @8
    vg
    @7
    @0
    @2
    @7
    wcel
    #
    wa
    @8
    @6
    @5
    cU
    wcel
    #
    @11
    @0
    @3
    @7
    wss
    @12
    @2
    @7
    snssi
    @7
    cR
    cU
    @3
    @4
    @9
    @10
    lpiss.u
    rspcl
    sylan2
    @1
    @5
    cU
    eleq1
    syl5ibrcom
    rexlimdva
    sylbid
    ssrdv
end
