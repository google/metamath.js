include "csuc.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "nfsn.mm"
include "nfun.mm"
include "nfcxfr.mm"

theorem nfsuc
  let vx: setvar x
  let cA: class A
  assume nfsuc.1: |- F/_ x A


  assert |- F/_ x suc A

  proof
    vx
    cA
    csuc
    cA
    cA
    csn
    #
    cun
    cA
    df-suc
    vx
    cA
    @0
    nfsuc.1
    vx
    cA
    nfsuc.1
    nfsn
    nfun
    nfcxfr
end
