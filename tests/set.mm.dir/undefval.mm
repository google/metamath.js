include "wcel.mm"
include "cvv.mm"
include "cuni.mm"
include "cpw.mm"
include "cund.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "uniexg.mm"
include "pwexg.mm"
include "syl.mm"
include "cv.mm"
include "unieq.mm"
include "pweqd.mm"
include "df-undef.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem undefval
  let cS: class S
  let cV: class V
  let vs: setvar s


  assert |- ( S e. V -> ( Undef ` S ) = ~P U. S )

  proof
    cS
    cV
    wcel
    #
    cS
    cvv
    wcel
    cS
    cuni
    #
    cpw
    #
    cvv
    wcel
    #
    cS
    cund
    cfv
    @2
    wceq
    cS
    cV
    elex
    @0
    @1
    cvv
    wcel
    @3
    cS
    cV
    uniexg
    @1
    cvv
    pwexg
    syl
    vs
    cS
    vs
    cv
    #
    cuni
    #
    cpw
    @2
    cvv
    cvv
    cund
    @4
    cS
    wceq
    @5
    @1
    @4
    cS
    unieq
    pweqd
    vs
    df-undef
    fvmptg
    syl2anc
end
