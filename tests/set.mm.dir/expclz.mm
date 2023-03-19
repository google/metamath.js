include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "csn.mm"
include "expclzlem.mm"
include "eldifad.mm"

theorem expclz
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ N ) e. CC )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cN
    cz
    wcel
    w3a
    cA
    cN
    cexp
    co
    cc
    cc0
    csn
    cA
    cN
    expclzlem
    eldifad
end
