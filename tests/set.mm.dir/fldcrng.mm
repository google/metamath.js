include "cdrng.mm"
include "wcel.mm"
include "ccm2.mm"
include "wa.mm"
include "crngo.mm"
include "cfld.mm"
include "ccring.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "crn.mm"
include "cgi.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "eqid.mm"
include "drngoi.mm"
include "simpld.mm"
include "anim1i.mm"
include "df-fld.mm"
include "elin2.mm"
include "iscrngo.mm"
include "3imtr4i.mm"

theorem fldcrng
  let cK: class K


  assert |- ( K e. Fld -> K e. CRingOps )

  proof
    cK
    cdrng
    wcel
    #
    cK
    ccm2
    wcel
    #
    wa
    cK
    crngo
    wcel
    #
    @1
    wa
    cK
    cfld
    wcel
    cK
    ccring
    wcel
    @0
    @2
    @1
    @0
    @2
    cK
    c2nd
    cfv
    #
    cK
    c1st
    cfv
    #
    crn
    #
    @4
    cgi
    cfv
    #
    csn
    cdif
    #
    @7
    cxp
    cres
    cgr
    wcel
    cK
    @4
    @3
    @5
    @6
    @4
    eqid
    @3
    eqid
    @5
    eqid
    @6
    eqid
    drngoi
    simpld
    anim1i
    cK
    cdrng
    ccm2
    cfld
    df-fld
    elin2
    cK
    iscrngo
    3imtr4i
end
