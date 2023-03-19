include "cv.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfsupp.mm"
include "df-fsupp.mm"
include "relopabi.mm"

theorem relfsupp
  let vr: setvar r
  let vz: setvar z


  assert |- Rel finSupp

  proof
    vr
    cv
    #
    wfun
    @0
    vz
    cv
    csupp
    co
    cfn
    wcel
    wa
    vr
    vz
    cfsupp
    vz
    vr
    df-fsupp
    relopabi
end
