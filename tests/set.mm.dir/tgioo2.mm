include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "eqid.mm"
include "cc.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cmopn.mm"
include "wceq.mm"
include "cnxmet.mm"
include "ax-resscn.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "mp2an.mm"
include "tgioo.mm"

theorem tgioo2
  let cJ: class J
  assume tgioo2.1: |- J = ( TopOpen ` CCfld )


  assert |- ( topGen ` ran (,) ) = ( J |`t RR )

  proof
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    cres
    #
    cJ
    cr
    crest
    co
    #
    @1
    eqid
    #
    @0
    cc
    cxmt
    cfv
    wcel
    cr
    cc
    wss
    @2
    @1
    cmopn
    cfv
    #
    wceq
    cnxmet
    ax-resscn
    @0
    @1
    cJ
    @4
    cc
    cr
    @3
    cJ
    tgioo2.1
    cnfldtopn
    @4
    eqid
    metrest
    mp2an
    tgioo
end
