include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cstv.mm"
include "cfv.mm"
include "ccj.mm"
include "wceq.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "cphsca.mm"
include "fveq2d.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "cnfldcj.mm"
include "ressstarv.mm"
include "ax-mp.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "fveq1d.mm"
include "csr.mm"
include "cphl.mm"
include "cphphl.mm"
include "phlsrng.mm"
include "syl.mm"
include "srngcl.mm"
include "sylan.mm"
include "eqeltrrd.mm"

theorem cphcjcl
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ A e. K ) -> ( * ` A ) e. K )

  proof
    cW
    ccph
    wcel
    #
    cA
    cK
    wcel
    #
    wa
    #
    cA
    cF
    cstv
    cfv
    #
    cfv
    #
    cA
    ccj
    cfv
    cK
    @2
    cA
    @3
    ccj
    @0
    @3
    ccj
    wceq
    @1
    @0
    @3
    ccnfld
    cK
    cress
    co
    #
    cstv
    cfv
    #
    ccj
    @0
    cF
    @5
    cstv
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsca
    fveq2d
    cK
    cvv
    wcel
    ccj
    @6
    wceq
    cK
    cF
    cbs
    cfv
    cvv
    cphsca.k
    cF
    cbs
    fvex
    eqeltri
    cK
    ccnfld
    @5
    ccj
    cvv
    @5
    eqid
    cnfldcj
    ressstarv
    ax-mp
    syl6eqr
    adantr
    fveq1d
    @0
    cF
    csr
    wcel
    #
    @1
    @4
    cK
    wcel
    @0
    cW
    cphl
    wcel
    @7
    cW
    cphphl
    cF
    cW
    cphsca.f
    phlsrng
    syl
    cK
    cF
    @3
    cA
    @3
    eqid
    cphsca.k
    srngcl
    sylan
    eqeltrrd
end
