include "wcel.mm"
include "c1.mm"
include "creps.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "cs1.mm"
include "cfzo.mm"
include "cxp.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "repsconst.mm"
include "mpan2.mm"
include "fzo01.mm"
include "a1i.mm"
include "xpeq1d.mm"
include "cvv.mm"
include "c0ex.mm"
include "xpsng.mm"
include "mpan.mm"
include "3eqtrd.mm"
include "s1val.mm"
include "eqtr4d.mm"

theorem repsw1
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( S repeatS 1 ) = <" S "> )

  proof
    cS
    cV
    wcel
    #
    cS
    c1
    creps
    co
    #
    cc0
    cS
    cop
    csn
    #
    cS
    cs1
    @0
    @1
    cc0
    c1
    cfzo
    co
    #
    cS
    csn
    #
    cxp
    #
    cc0
    csn
    #
    @4
    cxp
    #
    @2
    @0
    c1
    cn0
    wcel
    @1
    @5
    wceq
    1nn0
    cS
    c1
    cV
    repsconst
    mpan2
    @0
    @3
    @6
    @4
    @3
    @6
    wceq
    @0
    fzo01
    a1i
    xpeq1d
    cc0
    cvv
    wcel
    @0
    @7
    @2
    wceq
    c0ex
    cc0
    cS
    cvv
    cV
    xpsng
    mpan
    3eqtrd
    cS
    cV
    s1val
    eqtr4d
end
