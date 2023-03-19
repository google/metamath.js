include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "csts.mm"
include "df-sets.mm"
include "reldmmpt2.mm"

theorem reldmsets
  let ve: setvar e
  let vs: setvar s
  let cA: class A
  let cB: class B
  let cS: class S


  assert |- Rel dom sSet

  proof
    vs
    ve
    cvv
    cvv
    vs
    cv
    cvv
    ve
    cv
    csn
    #
    cdm
    cdif
    cres
    @0
    cun
    csts
    ve
    vs
    df-sets
    reldmmpt2
end
