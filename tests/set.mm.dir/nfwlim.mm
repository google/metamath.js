include "cwlim.mm"
include "cv.mm"
include "cinf.mm"
include "wne.mm"
include "cpred.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "crab.mm"
include "df-wlim.mm"
include "nfcv.mm"
include "nfinf.mm"
include "nfne.mm"
include "nfpred.mm"
include "nfsup.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfrab.mm"
include "nfcxfr.mm"

theorem nfwlim
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vy: setvar y
  assume nfwlim.1: |- F/_ x R
  assume nfwlim.2: |- F/_ x A


  assert |- F/_ x WLim ( R , A )

  proof
    vx
    cA
    cR
    cwlim
    vy
    cv
    #
    cA
    cA
    cR
    cinf
    #
    wne
    #
    @0
    cA
    cR
    @0
    cpred
    #
    cA
    cR
    csup
    #
    wceq
    #
    wa
    #
    vy
    cA
    crab
    vy
    cA
    cR
    df-wlim
    @6
    vx
    vy
    cA
    @2
    @5
    vx
    vx
    @0
    @1
    vx
    @0
    nfcv
    #
    vx
    cA
    cA
    cR
    nfwlim.2
    nfwlim.2
    nfwlim.1
    nfinf
    nfne
    vx
    @0
    @4
    vx
    @3
    cA
    cR
    vx
    cA
    cR
    @0
    nfwlim.1
    nfwlim.2
    @7
    nfpred
    nfwlim.2
    nfwlim.1
    nfsup
    nfeq2
    nfan
    nfwlim.2
    nfrab
    nfcxfr
end
