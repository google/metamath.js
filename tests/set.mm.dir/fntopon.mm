include "ctopon.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "funtopon.mm"
include "dmtopon.mm"
include "df-fn.mm"
include "mpbir2an.mm"

theorem fntopon
  let vx: setvar x
  let vy: setvar y


  assert |- TopOn Fn _V

  proof
    ctopon
    cvv
    wfn
    ctopon
    wfun
    ctopon
    cdm
    cvv
    wceq
    funtopon
    dmtopon
    ctopon
    cvv
    df-fn
    mpbir2an
end
