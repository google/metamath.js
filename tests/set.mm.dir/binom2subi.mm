include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "binom2sub.mm"
include "mp2an.mm"

theorem binom2subi
  let cA: class A
  let cB: class B
  assume binom2subi.1: |- A e. CC
  assume binom2subi.2: |- B e. CC


  assert |- ( ( A - B ) ^ 2 ) = ( ( ( A ^ 2 ) - ( 2 x. ( A x. B ) ) ) + ( B ^ 2 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmin
    co
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    c2
    cA
    cB
    cmul
    co
    cmul
    co
    cmin
    co
    cB
    c2
    cexp
    co
    caddc
    co
    wceq
    binom2subi.1
    binom2subi.2
    cA
    cB
    binom2sub
    mp2an
end
