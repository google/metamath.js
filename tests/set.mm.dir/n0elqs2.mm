include "c0.mm"
include "cqs.mm"
include "wcel.mm"
include "wn.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "n0elqs.mm"
include "ssdmres.mm"
include "bitri.mm"

theorem n0elqs2
  let cA: class A
  let cR: class R


  assert |- ( -. (/) e. ( A /. R ) <-> dom ( R |` A ) = A )

  proof
    c0
    cA
    cR
    cqs
    wcel
    wn
    cA
    cR
    cdm
    wss
    cR
    cA
    cres
    cdm
    cA
    wceq
    cA
    cR
    n0elqs
    cA
    cR
    ssdmres
    bitri
end
