include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "xpfi.mm"
include "anidms.mm"
include "eqid.mm"
include "frlmsca.mm"
include "ancoms.mm"
include "sylan.mm"
include "matsca.mm"
include "eqtrd.mm"

theorem matsca2
  let cA: class A
  let cR: class R
  let cN: class N
  let cV: class V
  assume matsca2.a: |- A = ( N Mat R )


  assert |- ( ( N e. Fin /\ R e. V ) -> R = ( Scalar ` A ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    cR
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    csca
    cfv
    #
    cA
    csca
    cfv
    @0
    @2
    cfn
    wcel
    #
    @1
    cR
    @4
    wceq
    #
    @0
    @5
    cN
    cN
    xpfi
    anidms
    @1
    @5
    @6
    cR
    @3
    @2
    cV
    cfn
    @3
    eqid
    #
    frlmsca
    ancoms
    sylan
    cA
    cR
    @3
    cN
    cV
    matsca2.a
    @7
    matsca
    eqtrd
end
