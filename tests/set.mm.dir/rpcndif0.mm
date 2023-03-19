include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "rpcnne0.mm"
include "eldifsn.mm"
include "sylibr.mm"

theorem rpcndif0
  let cA: class A


  assert |- ( A e. RR+ -> A e. ( CC \ { 0 } ) )

  proof
    cA
    crp
    wcel
    cA
    cc
    wcel
    cA
    cc0
    wne
    wa
    cA
    cc
    cc0
    csn
    cdif
    wcel
    cA
    rpcnne0
    cA
    cc
    cc0
    eldifsn
    sylibr
end
