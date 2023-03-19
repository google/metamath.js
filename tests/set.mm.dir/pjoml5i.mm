include "chj.mm"
include "co.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "chub1i.mm"
include "chjcli.mm"
include "pjoml2i.mm"
include "ax-mp.mm"

theorem pjoml5i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A vH ( ( _|_ ` A ) i^i ( A vH B ) ) ) = ( A vH B )

  proof
    cA
    cA
    cB
    chj
    co
    #
    wss
    cA
    cA
    cort
    cfv
    @0
    cin
    chj
    co
    @0
    wceq
    cA
    cB
    pjoml2.1
    pjoml2.2
    chub1i
    cA
    @0
    pjoml2.1
    cA
    cB
    pjoml2.1
    pjoml2.2
    chjcli
    pjoml2i
    ax-mp
end
