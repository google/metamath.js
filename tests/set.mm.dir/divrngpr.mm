include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "c2nd.mm"
include "cfv.mm"
include "cgi.mm"
include "c1st.mm"
include "wne.mm"
include "cidl.mm"
include "csn.mm"
include "crn.mm"
include "cpr.mm"
include "wceq.mm"
include "cprrng.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "eqid.mm"
include "isdrngo1.mm"
include "simplbi.mm"
include "dvrunz.mm"
include "divrngidl.mm"
include "smprngopr.mm"
include "syl3anc.mm"

theorem divrngpr
  let cR: class R


  assert |- ( R e. DivRingOps -> R e. PrRing )

  proof
    cR
    cdrng
    wcel
    #
    cR
    crngo
    wcel
    #
    cR
    c2nd
    cfv
    #
    cgi
    cfv
    #
    cR
    c1st
    cfv
    #
    cgi
    cfv
    #
    wne
    cR
    cidl
    cfv
    @5
    csn
    #
    @4
    crn
    #
    cpr
    wceq
    cR
    cprrng
    wcel
    @0
    @1
    @2
    @7
    @6
    cdif
    #
    @8
    cxp
    cres
    cgr
    wcel
    cR
    @4
    @2
    @7
    @5
    @4
    eqid
    #
    @2
    eqid
    #
    @5
    eqid
    #
    @7
    eqid
    #
    isdrngo1
    simplbi
    cR
    @3
    @4
    @2
    @7
    @5
    @9
    @10
    @12
    @11
    @3
    eqid
    #
    dvrunz
    cR
    @4
    @2
    @7
    @5
    @9
    @10
    @12
    @11
    divrngidl
    cR
    @3
    @4
    @2
    @7
    @5
    @9
    @10
    @12
    @11
    @13
    smprngopr
    syl3anc
end
