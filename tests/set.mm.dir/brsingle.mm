include "cvv.mm"
include "cxp.mm"
include "csingle.mm"
include "cid.mm"
include "csn.mm"
include "df-singleton.mm"
include "wbr.mm"
include "wcel.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wceq.mm"
include "velsn.mm"
include "ideq.mm"
include "bitr4i.mm"
include "brtxpsd3.mm"

theorem brsingle
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume brsingle.1: |- A e. _V
  assume brsingle.2: |- B e. _V


  assert |- ( A Singleton B <-> B = { A } )

  proof
    vx
    cA
    cB
    cvv
    cvv
    cxp
    #
    csingle
    cid
    cA
    csn
    #
    brsingle.1
    brsingle.2
    df-singleton
    cA
    cB
    @0
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    brsingle.1
    brsingle.2
    cA
    cB
    cvv
    cvv
    brxp
    mpbir2an
    vx
    cv
    #
    @1
    wcel
    @2
    cA
    wceq
    @2
    cA
    cid
    wbr
    vx
    cA
    velsn
    @2
    cA
    brsingle.1
    ideq
    bitr4i
    brtxpsd3
end
