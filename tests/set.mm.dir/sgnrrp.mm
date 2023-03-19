include "crp.mm"
include "wcel.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "sgnp.mm"
include "syl2anc.mm"

theorem sgnrrp
  let cA: class A


  assert |- ( A e. RR+ -> ( sgn ` A ) = 1 )

  proof
    cA
    crp
    wcel
    cA
    cxr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    csgn
    cfv
    c1
    wceq
    cA
    rpxr
    cA
    rpgt0
    cA
    sgnp
    syl2anc
end
