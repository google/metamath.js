include "cin.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "nfcri.mm"
include "r19.41.mm"
include "elin.mm"
include "rexbii.mm"
include "eliun.mm"
include "anbi1i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iunin1f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume iunin1f.1: |- F/_ x C


  assert |- U_ x e. A ( B i^i C ) = ( U_ x e. A B i^i C )

  proof
    vy
    vx
    cA
    cB
    cC
    cin
    #
    ciun
    #
    vx
    cA
    cB
    ciun
    #
    cC
    cin
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    @2
    wcel
    #
    @4
    cC
    wcel
    #
    wa
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @4
    cB
    wcel
    #
    @8
    wa
    #
    vx
    cA
    wrex
    @10
    vx
    cA
    wrex
    #
    @8
    wa
    @6
    @9
    @10
    @8
    vx
    cA
    vx
    vy
    cC
    iunin1f.1
    nfcri
    r19.41
    @5
    @11
    vx
    cA
    @4
    cB
    cC
    elin
    rexbii
    @7
    @12
    @8
    vx
    @4
    cA
    cB
    eliun
    anbi1i
    3bitr4i
    vx
    @4
    cA
    @0
    eliun
    @4
    @2
    cC
    elin
    3bitr4i
    eqriv
end
