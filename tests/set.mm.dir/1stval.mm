include "cvv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "sneq.mm"
include "dmeqd.mm"
include "unieqd.mm"
include "df-1st.mm"
include "snex.mm"
include "dmex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "snprc.mm"
include "biimpi.mm"
include "dm0.mm"
include "syl6eq.mm"
include "uni0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem 1stval
  let cA: class A
  let vx: setvar x


  assert |- ( 1st ` A ) = U. dom { A }

  proof
    cA
    cvv
    wcel
    #
    cA
    c1st
    cfv
    #
    cA
    csn
    #
    cdm
    #
    cuni
    #
    wceq
    vx
    cA
    vx
    cv
    #
    csn
    #
    cdm
    #
    cuni
    @4
    cvv
    c1st
    @5
    cA
    wceq
    #
    @7
    @3
    @8
    @6
    @2
    @5
    cA
    sneq
    dmeqd
    unieqd
    vx
    df-1st
    @3
    @2
    cA
    snex
    dmex
    uniex
    fvmpt
    @0
    wn
    #
    @1
    c0
    @4
    cA
    c1st
    fvprc
    @9
    @4
    c0
    cuni
    c0
    @9
    @3
    c0
    @9
    @3
    c0
    cdm
    c0
    @9
    @2
    c0
    @9
    @2
    c0
    wceq
    cA
    snprc
    biimpi
    dmeqd
    dm0
    syl6eq
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
end
