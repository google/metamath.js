include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "cvv.mm"
include "cbday.mm"
include "cfv.mm"
include "wceq.mm"
include "dmexg.mm"
include "cv.mm"
include "dmeq.mm"
include "df-bday.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem bdayval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> ( bday ` A ) = dom A )

  proof
    cA
    csur
    wcel
    cA
    cdm
    #
    cvv
    wcel
    cA
    cbday
    cfv
    @0
    wceq
    cA
    csur
    dmexg
    vx
    cA
    vx
    cv
    #
    cdm
    @0
    csur
    cvv
    cbday
    @1
    cA
    dmeq
    vx
    df-bday
    fvmptg
    mpdan
end
