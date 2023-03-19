include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cmul.mm"
include "csqrt.mm"
include "absval.mm"
include "oveq1d.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cjmulrcl.mm"
include "cjmulge0.mm"
include "resqrtth.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem absvalsq
  let cA: class A


  assert |- ( A e. CC -> ( ( abs ` A ) ^ 2 ) = ( A x. ( * ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c2
    cexp
    co
    cA
    cA
    ccj
    cfv
    cmul
    co
    #
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    @2
    @0
    @1
    @3
    c2
    cexp
    cA
    absval
    oveq1d
    @0
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @4
    @2
    wceq
    cA
    cjmulrcl
    cA
    cjmulge0
    @2
    resqrtth
    syl2anc
    eqtrd
end
