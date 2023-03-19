include "crp.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rpre.mm"
include "rpge0.mm"
include "resqrtcl.mm"
include "syl2anc.mm"
include "clt.mm"
include "rpgt0.mm"
include "sqrtgt0.mm"
include "elrpd.mm"

theorem rpsqrtcl
  let cA: class A


  assert |- ( A e. RR+ -> ( sqrt ` A ) e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cA
    csqrt
    cfv
    #
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    @1
    cr
    wcel
    cA
    rpre
    #
    cA
    rpge0
    cA
    resqrtcl
    syl2anc
    @0
    @2
    cc0
    cA
    clt
    wbr
    cc0
    @1
    clt
    wbr
    @3
    cA
    rpgt0
    cA
    sqrtgt0
    syl2anc
    elrpd
end
