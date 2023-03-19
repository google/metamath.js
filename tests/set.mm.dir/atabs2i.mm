include "cat.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "cin.mm"
include "wceq.mm"
include "chjcli.mm"
include "atabsi.mm"
include "chjassi.mm"
include "chjidmi.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "sseq2i.mm"
include "notbii.mm"
include "chabs2i.mm"
include "eqeq2i.mm"
include "3imtr3g.mm"

theorem atabs2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume atabs.1: |- A e. CH
  assume atabs.2: |- B e. CH


  assert |- ( C e. HAtoms -> ( -. C C_ ( A vH B ) -> ( ( A vH C ) i^i ( A vH B ) ) = A ) )

  proof
    cC
    cat
    wcel
    cC
    cA
    cA
    cB
    chj
    co
    #
    chj
    co
    #
    wss
    #
    wn
    cA
    cC
    chj
    co
    @0
    cin
    #
    cA
    @0
    cin
    #
    wceq
    cC
    @0
    wss
    #
    wn
    @3
    cA
    wceq
    cA
    @0
    cC
    atabs.1
    cA
    cB
    atabs.1
    atabs.2
    chjcli
    atabsi
    @2
    @5
    @1
    @0
    cC
    cA
    cA
    chj
    co
    #
    cB
    chj
    co
    @1
    @0
    cA
    cA
    cB
    atabs.1
    atabs.1
    atabs.2
    chjassi
    @6
    cA
    cB
    chj
    cA
    atabs.1
    chjidmi
    oveq1i
    eqtr3i
    sseq2i
    notbii
    @4
    cA
    @3
    cA
    cB
    atabs.1
    atabs.2
    chabs2i
    eqeq2i
    3imtr3g
end
