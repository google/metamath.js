include "c0.mm"
include "cv.mm"
include "wf.mm"
include "copab.mm"
include "cusgr.mm"
include "wss.mm"
include "cvv.mm"
include "wnel.mm"
include "eqid.mm"
include "griedg0ssusgr.mm"
include "griedg0prc.mm"
include "prcssprc.mm"
include "mp2an.mm"

theorem usgrprc
  let ve: setvar e
  let vv: setvar v


  assert |- USGraph e/ _V

  proof
    c0
    c0
    ve
    cv
    wf
    vv
    ve
    copab
    #
    cusgr
    wss
    @0
    cvv
    wnel
    cusgr
    cvv
    wnel
    vv
    @0
    ve
    @0
    eqid
    #
    griedg0ssusgr
    vv
    @0
    ve
    @1
    griedg0prc
    @0
    cusgr
    prcssprc
    mp2an
end
