include "wcel.mm"
include "cid.mm"
include "wbr.mm"
include "wceq.mm"
include "eqid.mm"
include "ideqg.mm"
include "mpbiri.mm"

theorem ididg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A _I A )

  proof
    cA
    cV
    wcel
    cA
    cA
    cid
    wbr
    cA
    cA
    wceq
    cA
    eqid
    cA
    cA
    cV
    ideqg
    mpbiri
end
