include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wn.mm"
include "c0.mm"
include "ndmov.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem ndmovcl
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )
  assume ndmovcl.2: |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S )
  assume ndmovcl.3: |- (/) e. S


  assert |- ( A F B ) e. S

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cA
    cB
    cF
    co
    #
    cS
    wcel
    ndmovcl.2
    @0
    wn
    @1
    c0
    cS
    cA
    cB
    cS
    cF
    ndmov.1
    ndmov
    ndmovcl.3
    syl6eqel
    pm2.61i
end
