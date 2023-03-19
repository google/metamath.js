include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "eqid.mm"
include "elsng.mm"
include "mpbiri.mm"

theorem snidg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A e. { A } )

  proof
    cA
    cV
    wcel
    cA
    cA
    csn
    wcel
    cA
    cA
    wceq
    cA
    eqid
    cA
    cA
    cV
    elsng
    mpbiri
end
