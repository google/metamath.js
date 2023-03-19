include "csur.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "cbday.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "nofun.mm"
include "bdayval.mm"
include "eqcomd.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem nofnbday
  let cA: class A


  assert |- ( A e. No -> A Fn ( bday ` A ) )

  proof
    cA
    csur
    wcel
    #
    cA
    wfun
    cA
    cdm
    #
    cA
    cbday
    cfv
    #
    wceq
    cA
    @2
    wfn
    cA
    nofun
    @0
    @2
    @1
    cA
    bdayval
    eqcomd
    cA
    @2
    df-fn
    sylanbrc
end
