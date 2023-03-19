include "cmpt.mm"
include "cres.mm"
include "cin.mm"
include "resres.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "inss1.mm"
include "3eqtr3i.mm"

theorem resmpt3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ( x e. A |-> C ) |` B ) = ( x e. ( A i^i B ) |-> C )

  proof
    vx
    cA
    cC
    cmpt
    #
    cA
    cres
    #
    cB
    cres
    @0
    cA
    cB
    cin
    #
    cres
    #
    @0
    cB
    cres
    vx
    @2
    cC
    cmpt
    #
    @0
    cA
    cB
    resres
    @1
    @0
    cB
    cA
    cA
    wss
    @1
    @0
    wceq
    cA
    ssid
    vx
    cA
    cA
    cC
    resmpt
    ax-mp
    reseq1i
    @2
    cA
    wss
    @3
    @4
    wceq
    cA
    cB
    inss1
    vx
    cA
    @2
    cC
    resmpt
    ax-mp
    3eqtr3i
end
