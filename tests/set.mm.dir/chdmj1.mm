include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "chdmm4.mm"
include "fveq2d.mm"
include "wceq.mm"
include "choccl.mm"
include "chincl.mm"
include "syl2an.mm"
include "ococ.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem chdmj1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( _|_ ` ( A vH B ) ) = ( ( _|_ ` A ) i^i ( _|_ ` B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cin
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cA
    cB
    chj
    co
    #
    cort
    cfv
    @5
    @2
    @6
    @8
    cort
    cA
    cB
    chdmm4
    fveq2d
    @2
    @5
    cch
    wcel
    #
    @7
    @5
    wceq
    @0
    @3
    cch
    wcel
    @4
    cch
    wcel
    @9
    @1
    cA
    choccl
    cB
    choccl
    @3
    @4
    chincl
    syl2an
    @5
    ococ
    syl
    eqtr3d
end
