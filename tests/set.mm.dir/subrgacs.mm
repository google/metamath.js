include "crg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cmgp.mm"
include "csubmnd.mm"
include "cin.mm"
include "cacs.mm"
include "cv.mm"
include "wa.mm"
include "eqid.mm"
include "issubrg3.mm"
include "elin.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "cpw.mm"
include "cmre.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mreacs.mm"
include "mp1i.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "subgacs.mm"
include "syl.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "submacs.mm"
include "mreincl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem subrgacs
  let cB: class B
  let cR: class R
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume subrgacs.b: |- B = ( Base ` R )


  assert |- ( R e. Ring -> ( SubRing ` R ) e. ( ACS ` B ) )

  proof
    cR
    crg
    wcel
    #
    cR
    csubrg
    cfv
    #
    cR
    csubg
    cfv
    #
    cR
    cmgp
    cfv
    #
    csubmnd
    cfv
    #
    cin
    #
    cB
    cacs
    cfv
    #
    @0
    vx
    @1
    @5
    @0
    vx
    cv
    #
    @1
    wcel
    @7
    @2
    wcel
    @7
    @4
    wcel
    wa
    @7
    @5
    wcel
    cR
    @7
    @3
    @3
    eqid
    #
    issubrg3
    @7
    @2
    @4
    elin
    syl6bbr
    eqrdv
    @0
    @6
    cB
    cpw
    #
    cmre
    cfv
    wcel
    #
    @2
    @6
    wcel
    #
    @4
    @6
    wcel
    #
    @5
    @6
    wcel
    cB
    cvv
    wcel
    @10
    @0
    cB
    cR
    cbs
    cfv
    cvv
    subrgacs.b
    cR
    cbs
    fvex
    eqeltri
    cvv
    cB
    mreacs
    mp1i
    @0
    cR
    cgrp
    wcel
    @11
    cR
    ringgrp
    cB
    cR
    subrgacs.b
    subgacs
    syl
    @0
    @3
    cmnd
    wcel
    @12
    cR
    @3
    @8
    ringmgp
    cB
    @3
    cB
    cR
    @3
    @8
    subrgacs.b
    mgpbas
    submacs
    syl
    @2
    @4
    @6
    @9
    mreincl
    syl3anc
    eqeltrd
end
