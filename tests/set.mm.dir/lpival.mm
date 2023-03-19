include "crg.mm"
include "wcel.mm"
include "clpidl.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "csn.mm"
include "crsp.mm"
include "ciun.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sneqd.mm"
include "iuneq12d.mm"
include "df-lpidl.mm"
include "crn.mm"
include "c0.mm"
include "cun.mm"
include "fvex.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "wss.mm"
include "iunss.mm"
include "fvrn0.mm"
include "snssi.mm"
include "ax-mp.mm"
include "a1i.mm"
include "mprgbir.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "iuneq1.mm"
include "fveq1i.mm"
include "sneqi.mm"
include "iuneq2i.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem lpival
  let cB: class B
  let cP: class P
  let cR: class R
  let vg: setvar g
  let cK: class K
  let vr: setvar r
  let cU: class U
  let cI: class I
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpival.k: |- K = ( RSpan ` R )
  assume lpival.b: |- B = ( Base ` R )

  disjoint R g
  disjoint P g
  disjoint B g
  disjoint K g
  disjoint R r
  disjoint g r
  disjoint P r
  disjoint B r
  disjoint K r
  disjoint U g
  disjoint I g
  disjoint .0. g
  assert |- ( R e. Ring -> P = U_ g e. B { ( K ` { g } ) } )

  proof
    cR
    crg
    wcel
    cR
    clpidl
    cfv
    vg
    cR
    cbs
    cfv
    #
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
    csn
    #
    ciun
    #
    cP
    vg
    cB
    @2
    cK
    cfv
    #
    csn
    #
    ciun
    #
    vr
    cR
    vg
    vr
    cv
    #
    cbs
    cfv
    #
    @2
    @10
    crsp
    cfv
    #
    cfv
    #
    csn
    #
    ciun
    @6
    crg
    clpidl
    @10
    cR
    wceq
    #
    vg
    @11
    @0
    @14
    @5
    @10
    cR
    cbs
    fveq2
    @15
    @13
    @4
    @15
    @2
    @12
    @3
    @10
    cR
    crsp
    fveq2
    fveq1d
    sneqd
    iuneq12d
    vr
    vg
    df-lpidl
    @6
    @3
    crn
    #
    c0
    csn
    #
    cun
    #
    @16
    @17
    @3
    cR
    crsp
    fvex
    rnex
    p0ex
    unex
    @6
    @18
    wss
    @5
    @18
    wss
    #
    vg
    @0
    vg
    @0
    @5
    @18
    iunss
    @19
    @1
    @0
    wcel
    #
    @4
    @18
    wcel
    @19
    @3
    @2
    fvrn0
    @4
    @18
    snssi
    ax-mp
    a1i
    mprgbir
    ssexi
    fvmpt
    lpival.p
    @9
    vg
    @0
    @8
    ciun
    #
    @6
    cB
    @0
    wceq
    @9
    @21
    wceq
    lpival.b
    vg
    cB
    @0
    @8
    iuneq1
    ax-mp
    vg
    @0
    @8
    @5
    @8
    @5
    wceq
    @20
    @7
    @4
    @2
    cK
    @3
    lpival.k
    fveq1i
    sneqi
    a1i
    iuneq2i
    eqtri
    3eqtr4g
end
