include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cc.mm"
include "wceq.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "wss.mm"
include "cphsubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "sselda.mm"
include "absval.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "cphcjcl.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "cjmulrcld.mm"
include "cjmulge0d.mm"
include "cphsqrtcl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"

theorem cphabscl
  let cA: class A
  let cF: class F
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume cphsca.f: |- F = ( Scalar ` W )
  assume cphsca.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ A e. K ) -> ( abs ` A ) e. K )

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
    cabs
    cfv
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cK
    @2
    cA
    cc
    wcel
    @3
    @6
    wceq
    @0
    cK
    cc
    cA
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    cK
    cc
    wss
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsubrg
    #
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    sselda
    #
    cA
    absval
    syl
    @2
    @0
    @5
    cK
    wcel
    #
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    @6
    cK
    wcel
    @0
    @1
    simpl
    @2
    @7
    @1
    @4
    cK
    wcel
    @10
    @0
    @7
    @1
    @8
    adantr
    @0
    @1
    simpr
    cA
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphcjcl
    cK
    ccnfld
    cmul
    cA
    @4
    cnfldmul
    subrgmcl
    syl3anc
    @2
    cA
    @9
    cjmulrcld
    @2
    cA
    @9
    cjmulge0d
    @5
    cF
    cK
    cW
    cphsca.f
    cphsca.k
    cphsqrtcl
    syl13anc
    eqeltrd
end
