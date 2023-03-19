include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "expclzlem.mm"
include "eldifsni.mm"
include "syl.mm"

theorem expne0i
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ N ) =/= 0 )

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
    #
    cc
    cc0
    csn
    cdif
    wcel
    @0
    cc0
    wne
    cA
    cN
    expclzlem
    @0
    cc
    cc0
    eldifsni
    syl
end
