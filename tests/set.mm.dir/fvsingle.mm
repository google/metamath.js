include "cvv.mm"
include "wcel.mm"
include "csingle.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "sneq.mm"
include "eqeq12d.mm"
include "wbr.mm"
include "eqid.mm"
include "vex.mm"
include "snex.mm"
include "brsingle.mm"
include "mpbir.mm"
include "wfn.mm"
include "wb.mm"
include "fnsingle.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "snprc.mm"
include "biimpi.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem fvsingle
  let cA: class A
  let vx: setvar x


  assert |- ( Singleton ` A ) = { A }

  proof
    cA
    cvv
    wcel
    #
    cA
    csingle
    cfv
    #
    cA
    csn
    #
    wceq
    #
    vx
    cv
    #
    csingle
    cfv
    #
    @4
    csn
    #
    wceq
    #
    @3
    vx
    cA
    cvv
    @4
    cA
    wceq
    @5
    @1
    @6
    @2
    @4
    cA
    csingle
    fveq2
    @4
    cA
    sneq
    eqeq12d
    @7
    @4
    @6
    csingle
    wbr
    #
    @8
    @6
    @6
    wceq
    @6
    eqid
    @4
    @6
    vx
    vex
    #
    @4
    snex
    brsingle
    mpbir
    csingle
    cvv
    wfn
    @4
    cvv
    wcel
    @7
    @8
    wb
    fnsingle
    @9
    cvv
    @4
    @6
    csingle
    fnbrfvb
    mp2an
    mpbir
    vtoclg
    @0
    wn
    #
    @1
    c0
    @2
    cA
    csingle
    fvprc
    @10
    @2
    c0
    wceq
    cA
    snprc
    biimpi
    eqtr4d
    pm2.61i
end
