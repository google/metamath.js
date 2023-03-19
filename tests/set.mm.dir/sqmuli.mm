include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "sqmul.mm"
include "mp2an.mm"

theorem sqmuli
  let cA: class A
  let cB: class B
  assume sqval.1: |- A e. CC
  assume sqmul.2: |- B e. CC


  assert |- ( ( A x. B ) ^ 2 ) = ( ( A ^ 2 ) x. ( B ^ 2 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
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
    sqval.1
    sqmul.2
    cA
    cB
    sqmul
    mp2an
end
