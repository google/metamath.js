include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cabs.mm"
include "cle.mm"
include "cr.mm"
include "wbr.mm"
include "cjmulrcl.mm"
include "cjmulge0.mm"
include "sqrtge0.mm"
include "syl2anc.mm"
include "absval.mm"
include "breqtrrd.mm"

theorem absge0
  let cA: class A


  assert |- ( A e. CC -> 0 <_ ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cc0
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
    cA
    cabs
    cfv
    cle
    @0
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    cc0
    @2
    cle
    wbr
    cA
    cjmulrcl
    cA
    cjmulge0
    @1
    sqrtge0
    syl2anc
    cA
    absval
    breqtrrd
end
