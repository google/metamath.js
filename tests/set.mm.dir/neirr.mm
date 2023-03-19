include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "eqid.mm"
include "nne.mm"
include "mpbir.mm"

theorem neirr
  let cA: class A


  assert |- -. A =/= A

  proof
    cA
    cA
    wne
    wn
    cA
    cA
    wceq
    cA
    eqid
    cA
    cA
    nne
    mpbir
end
