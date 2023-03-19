include "cxrs.mm"
include "cxr.mm"
include "cmnf.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "ccmn.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cmnd.mm"
include "eqid.mm"
include "xrs1cmn.mm"
include "csubmnd.mm"
include "cfv.mm"
include "xrge0subm.mm"
include "cvv.mm"
include "wss.mm"
include "wceq.mm"
include "xrex.mm"
include "difss.mm"
include "ssexi.mm"
include "cbs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "submss.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "submmnd.mm"
include "subcmn.mm"

theorem xrge0cmn



  assert |- ( RR*s |`s ( 0 [,] +oo ) ) e. CMnd

  proof
    cxrs
    cxr
    cmnf
    csn
    #
    cdif
    #
    cress
    co
    #
    ccmn
    wcel
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    cmnd
    wcel
    #
    @4
    ccmn
    wcel
    @2
    @2
    eqid
    #
    xrs1cmn
    @3
    @2
    csubmnd
    cfv
    wcel
    #
    @5
    @2
    @6
    xrge0subm
    #
    @3
    @4
    @2
    @2
    @3
    cress
    co
    #
    @4
    @1
    cvv
    wcel
    @3
    @1
    wss
    #
    @9
    @4
    wceq
    @1
    cxr
    xrex
    cxr
    @0
    difss
    #
    ssexi
    @7
    @10
    @8
    @1
    @3
    @2
    @1
    cxr
    wss
    @1
    @2
    cbs
    cfv
    wceq
    @11
    @1
    cxr
    @2
    cxrs
    @6
    xrsbas
    ressbas2
    ax-mp
    submss
    ax-mp
    @1
    @3
    cxrs
    cvv
    ressabs
    mp2an
    eqcomi
    #
    submmnd
    ax-mp
    @3
    @2
    @4
    @12
    subcmn
    mp2an
end
