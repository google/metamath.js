include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "clp.mm"
include "cun.mm"
include "cv.mm"
include "wo.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "wral.mm"
include "wi.mm"
include "neindisj.mm"
include "expr.mm"
include "adantr.mm"
include "wb.mm"
include "difsn.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "adantl.mm"
include "sylibrd.mm"
include "ex.mm"
include "ralrimdv.mm"
include "simpll.mm"
include "simplr.mm"
include "clsss3.mm"
include "sselda.mm"
include "islp2.mm"
include "syl3anc.mm"
include "orrd.mm"
include "elun.mm"
include "sylibr.mm"
include "ssrdv.mm"
include "sscls.mm"
include "lpsscls.mm"
include "unssd.mm"
include "eqssd.mm"

theorem clslp
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` S ) = ( S u. ( ( limPt ` J ) ` S ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    cS
    cJ
    clp
    cfv
    cfv
    #
    cun
    #
    @2
    vx
    @3
    @5
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @6
    @5
    wcel
    #
    @2
    @7
    wa
    #
    @6
    cS
    wcel
    #
    @6
    @4
    wcel
    #
    wo
    @8
    @9
    @10
    @11
    @9
    @10
    wn
    #
    vn
    cv
    #
    cS
    @6
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    vn
    @14
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    @11
    @9
    @12
    @17
    vn
    @18
    @9
    @12
    @13
    @18
    wcel
    #
    @17
    wi
    @9
    @12
    wa
    @20
    @13
    cS
    cin
    #
    c0
    wne
    #
    @17
    @9
    @20
    @22
    wi
    @12
    @2
    @7
    @20
    @22
    @6
    cS
    cJ
    @13
    cX
    lpfval.1
    neindisj
    expr
    adantr
    @12
    @17
    @22
    wb
    @9
    @12
    @16
    @21
    c0
    @12
    @15
    cS
    @13
    @6
    cS
    difsn
    ineq2d
    neeq1d
    adantl
    sylibrd
    ex
    ralrimdv
    @9
    @0
    @1
    @6
    cX
    wcel
    @11
    @19
    wb
    @0
    @1
    @7
    simpll
    @0
    @1
    @7
    simplr
    @2
    @3
    cX
    @6
    cS
    cJ
    cX
    lpfval.1
    clsss3
    sselda
    @6
    cS
    vn
    cJ
    cX
    lpfval.1
    islp2
    syl3anc
    sylibrd
    orrd
    @6
    cS
    @4
    elun
    sylibr
    ex
    ssrdv
    @2
    cS
    @4
    @3
    cS
    cJ
    cX
    lpfval.1
    sscls
    cS
    cJ
    cX
    lpfval.1
    lpsscls
    unssd
    eqssd
end
