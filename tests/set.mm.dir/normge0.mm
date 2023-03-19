include "chil.mm"
include "wcel.mm"
include "cc0.mm"
include "csp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cno.mm"
include "cle.mm"
include "hiidrcl.mm"
include "hiidge0.mm"
include "sqrtge0d.mm"
include "normval.mm"
include "breqtrrd.mm"

theorem normge0
  let cA: class A


  assert |- ( A e. ~H -> 0 <_ ( normh ` A ) )

  proof
    cA
    chil
    wcel
    #
    cc0
    cA
    cA
    csp
    co
    #
    csqrt
    cfv
    cA
    cno
    cfv
    cle
    @0
    @1
    cA
    hiidrcl
    cA
    hiidge0
    sqrtge0d
    cA
    normval
    breqtrrd
end
