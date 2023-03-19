include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "neirr.mm"
include "eldifsni.mm"
include "mto.mm"

theorem neldifsn
  let cA: class A
  let cB: class B


  assert |- -. A e. ( B \ { A } )

  proof
    cA
    cB
    cA
    csn
    cdif
    wcel
    cA
    cA
    wne
    cA
    neirr
    cA
    cB
    cA
    eldifsni
    mto
end
