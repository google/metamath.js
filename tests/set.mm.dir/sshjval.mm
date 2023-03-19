include "chil.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "elpw2.mm"
include "cv.mm"
include "wa.mm"
include "uneq12.mm"
include "fveq2d.mm"
include "df-chj.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "syl2anbr.mm"

theorem sshjval
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A vH B ) = ( _|_ ` ( _|_ ` ( A u. B ) ) ) )

  proof
    cA
    chil
    wss
    cA
    chil
    cpw
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    chj
    co
    cA
    cB
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wceq
    cB
    chil
    wss
    cA
    chil
    ax-hilex
    elpw2
    cB
    chil
    ax-hilex
    elpw2
    vx
    vy
    cA
    cB
    @0
    @0
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    @3
    chj
    @4
    cA
    wceq
    @5
    cB
    wceq
    wa
    #
    @7
    @2
    cort
    @8
    @6
    @1
    cort
    @4
    cA
    @5
    cB
    uneq12
    fveq2d
    fveq2d
    vx
    vy
    df-chj
    @2
    cort
    fvex
    ovmpt2a
    syl2anbr
end
