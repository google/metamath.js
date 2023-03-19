include "word.mm"
include "c0.mm"
include "wcel.mm"
include "c1o.mm"
include "wss.mm"
include "wne.mm"
include "ordgt0ge1.mm"
include "ord0eln0.mm"
include "bitr3d.mm"

theorem ordge1n0
  let cA: class A


  assert |- ( Ord A -> ( 1o C_ A <-> A =/= (/) ) )

  proof
    cA
    word
    c0
    cA
    wcel
    c1o
    cA
    wss
    cA
    c0
    wne
    cA
    ordgt0ge1
    cA
    ord0eln0
    bitr3d
end
