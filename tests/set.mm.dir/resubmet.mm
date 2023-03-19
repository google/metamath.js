include "cr.mm"
include "wss.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "xpss12.mm"
include "anidms.mm"
include "resabs1d.mm"
include "fveq2d.mm"
include "syl6reqr.mm"
include "cxmt.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "rexmet.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "tgioo.mm"
include "eqtri.mm"
include "metrest.mm"
include "mpan.mm"
include "eqtr4d.mm"

theorem resubmet
  let cA: class A
  let cR: class R
  let cJ: class J
  assume resubmet.1: |- R = ( topGen ` ran (,) )
  assume resubmet.2: |- J = ( MetOpen ` ( ( abs o. - ) |` ( A X. A ) ) )


  assert |- ( A C_ RR -> J = ( R |`t A ) )

  proof
    cA
    cr
    wss
    #
    cJ
    cabs
    cmin
    ccom
    #
    cr
    cr
    cxp
    #
    cres
    #
    cA
    cA
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    cR
    cA
    crest
    co
    #
    @0
    @6
    @1
    @4
    cres
    #
    cmopn
    cfv
    cJ
    @0
    @5
    @8
    cmopn
    @0
    @1
    @4
    @2
    @0
    @4
    @2
    wss
    cA
    cr
    cA
    cr
    xpss12
    anidms
    resabs1d
    fveq2d
    resubmet.2
    syl6reqr
    @3
    cr
    cxmt
    cfv
    wcel
    @0
    @7
    @6
    wceq
    @3
    @3
    eqid
    #
    rexmet
    @3
    @5
    cR
    @6
    cr
    cA
    @5
    eqid
    cR
    cioo
    crn
    ctg
    cfv
    @3
    cmopn
    cfv
    #
    resubmet.1
    @3
    @10
    @9
    @10
    eqid
    tgioo
    eqtri
    @6
    eqid
    metrest
    mpan
    eqtr4d
end
