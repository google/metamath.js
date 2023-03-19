include "cid.mm"
include "cres.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "funi.mm"
include "funres.mm"
include "ax-mp.mm"
include "dmresi.mm"
include "df-fn.mm"
include "mpbir2an.mm"

theorem fnresi
  let cA: class A


  assert |- ( _I |` A ) Fn A

  proof
    cid
    cA
    cres
    #
    cA
    wfn
    @0
    wfun
    #
    @0
    cdm
    cA
    wceq
    cid
    wfun
    @1
    funi
    cA
    cid
    funres
    ax-mp
    cA
    dmresi
    @0
    cA
    df-fn
    mpbir2an
end
