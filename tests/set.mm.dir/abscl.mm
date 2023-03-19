include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cr.mm"
include "absval.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cjmulrcl.mm"
include "cjmulge0.mm"
include "resqrtcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem abscl
  let cA: class A


  assert |- ( A e. CC -> ( abs ` A ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
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
    cr
    cA
    absval
    @0
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @2
    cr
    wcel
    cA
    cjmulrcl
    cA
    cjmulge0
    @1
    resqrtcl
    syl2anc
    eqeltrd
end
