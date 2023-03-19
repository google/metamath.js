include "ctop.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "csigagen.mm"
include "cv.mm"
include "wa.mm"
include "cuni.mm"
include "cdif.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "cldss.mm"
include "adantl.mm"
include "dfss4.mm"
include "sylib.mm"
include "topopn.mm"
include "difopn.mm"
include "sylan.mm"
include "csiga.mm"
include "crn.mm"
include "id.mm"
include "sgsiga.mm"
include "adantr.mm"
include "cvv.mm"
include "elex.mm"
include "sigagensiga.mm"
include "baselsiga.mm"
include "3syl.mm"
include "elsigagen.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem cldssbrsiga
  let cJ: class J
  let vx: setvar x


  assert |- ( J e. Top -> ( Clsd ` J ) C_ ( sigaGen ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cJ
    ccld
    cfv
    #
    cJ
    csigagen
    cfv
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    @0
    @4
    wa
    #
    cJ
    cuni
    #
    @6
    @3
    cdif
    #
    cdif
    #
    @3
    @2
    @5
    @3
    @6
    wss
    #
    @8
    @3
    wceq
    @4
    @9
    @0
    @3
    cJ
    @6
    @6
    eqid
    #
    cldss
    adantl
    @3
    @6
    dfss4
    sylib
    @0
    @4
    @7
    cJ
    wcel
    #
    @8
    @2
    wcel
    #
    @0
    @6
    cJ
    wcel
    @4
    @11
    cJ
    @6
    @10
    topopn
    @6
    @3
    cJ
    @6
    @10
    difopn
    sylan
    @0
    @11
    wa
    @2
    csiga
    crn
    cuni
    wcel
    #
    @6
    @2
    wcel
    #
    @7
    @2
    wcel
    @12
    @0
    @13
    @11
    @0
    cJ
    ctop
    @0
    id
    sgsiga
    adantr
    @0
    @14
    @11
    @0
    cJ
    cvv
    wcel
    @2
    @6
    csiga
    cfv
    wcel
    @14
    cJ
    ctop
    elex
    cJ
    cvv
    sigagensiga
    @6
    @2
    baselsiga
    3syl
    adantr
    cJ
    @7
    ctop
    elsigagen
    @6
    @7
    @2
    difelsiga
    syl3anc
    syldan
    eqeltrrd
    ex
    ssrdv
end
