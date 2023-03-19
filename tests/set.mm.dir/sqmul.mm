include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cn0.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "2nn0.mm"
include "mulexp.mm"
include "mp3an3.mm"

theorem sqmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A x. B ) ^ 2 ) = ( ( A ^ 2 ) x. ( B ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    c2
    cn0
    wcel
    cA
    cB
    cmul
    co
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cmul
    co
    wceq
    2nn0
    cA
    cB
    c2
    mulexp
    mp3an3
end
