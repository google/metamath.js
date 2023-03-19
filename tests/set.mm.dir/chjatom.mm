include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cv.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "atom1d.mm"
include "wi.mm"
include "spansnj.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "expd.mm"
include "adantl.mm"
include "com3l.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "imp.mm"

theorem chjatom
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( A +H B ) = ( A vH B ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    cA
    cB
    cph
    co
    #
    cA
    cB
    chj
    co
    #
    wceq
    #
    @1
    vx
    cv
    #
    c0v
    wne
    #
    cB
    @5
    csn
    cspn
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    @0
    @4
    vx
    cB
    atom1d
    @0
    @9
    @4
    vx
    chil
    @9
    @0
    @5
    chil
    wcel
    #
    @4
    @8
    @0
    @10
    @4
    wi
    wi
    @6
    @8
    @0
    @10
    @4
    @0
    @10
    wa
    @4
    @8
    cA
    @7
    cph
    co
    #
    cA
    @7
    chj
    co
    #
    wceq
    cA
    @5
    spansnj
    @8
    @2
    @11
    @3
    @12
    cB
    @7
    cA
    cph
    oveq2
    cB
    @7
    cA
    chj
    oveq2
    eqeq12d
    syl5ibr
    expd
    adantl
    com3l
    rexlimdv
    syl5bi
    imp
end
