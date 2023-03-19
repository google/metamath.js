include "ccat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "ccid.mm"
include "ciso.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "cinv.mm"
include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "chom.mm"
include "catidcl.mm"
include "catrid.mm"
include "issect2.mm"
include "anbi12d.mm"
include "mpbir2and.mm"
include "isinv.mm"
include "mpbird.mm"
include "inviso1.mm"
include "brcici.mm"

theorem cicref
  let cC: class C
  let cO: class O


  assert |- ( ( C e. Cat /\ O e. ( Base ` C ) ) -> O ( ~=c ` C ) O )

  proof
    cC
    ccat
    wcel
    #
    cO
    cC
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @1
    cC
    cO
    cC
    ccid
    cfv
    #
    cfv
    #
    cC
    ciso
    cfv
    #
    cO
    cO
    @6
    eqid
    #
    @1
    eqid
    #
    @0
    @2
    simpl
    #
    @0
    @2
    simpr
    #
    @10
    @3
    @1
    cC
    @5
    @5
    @6
    cC
    cinv
    cfv
    #
    cO
    cO
    @8
    @11
    eqid
    #
    @9
    @10
    @10
    @7
    @3
    @5
    @5
    cO
    cO
    @11
    co
    wbr
    @5
    @5
    cO
    cO
    cC
    csect
    cfv
    #
    co
    wbr
    #
    @14
    wa
    #
    @3
    @15
    @5
    @5
    cO
    cO
    cop
    cO
    cC
    cco
    cfv
    #
    co
    co
    @5
    wceq
    #
    @17
    @3
    @1
    cC
    @16
    @4
    @5
    cC
    chom
    cfv
    #
    cO
    cO
    @8
    @18
    eqid
    #
    @4
    eqid
    #
    @9
    @10
    @16
    eqid
    #
    @10
    @3
    @1
    cC
    @4
    @18
    cO
    @8
    @19
    @20
    @9
    @10
    catidcl
    #
    catrid
    #
    @23
    @3
    @14
    @17
    @14
    @17
    @3
    @1
    cC
    @13
    @16
    @4
    @5
    @5
    @18
    cO
    cO
    @8
    @19
    @21
    @20
    @13
    eqid
    #
    @9
    @10
    @10
    @22
    @22
    issect2
    #
    @25
    anbi12d
    mpbir2and
    @3
    @1
    cC
    @13
    @5
    @5
    @11
    cO
    cO
    @8
    @12
    @9
    @10
    @10
    @24
    isinv
    mpbird
    inviso1
    brcici
end
