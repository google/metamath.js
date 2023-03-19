include "chil.mm"
include "wss.mm"
include "wa.mm"
include "cpr.mm"
include "cuni.mm"
include "cort.mm"
include "cfv.mm"
include "cun.mm"
include "chsup.mm"
include "chj.mm"
include "co.mm"
include "cpw.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-hilex.mm"
include "elpw2.mm"
include "uniprg.mm"
include "syl2anbr.mm"
include "fveq2d.mm"
include "prssi.mm"
include "hsupval.mm"
include "syl.mm"
include "sshjval.mm"
include "3eqtr4rd.mm"

theorem sshjval3
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A vH B ) = ( \/H ` { A , B } ) )

  proof
    cA
    chil
    wss
    #
    cB
    chil
    wss
    #
    wa
    #
    cA
    cB
    cpr
    #
    cuni
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cA
    cB
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    @3
    chsup
    cfv
    #
    cA
    cB
    chj
    co
    @2
    @5
    @8
    cort
    @2
    @4
    @7
    cort
    @0
    cA
    chil
    cpw
    #
    wcel
    #
    cB
    @10
    wcel
    #
    @4
    @7
    wceq
    @1
    cA
    chil
    ax-hilex
    elpw2
    #
    cB
    chil
    ax-hilex
    elpw2
    #
    cA
    cB
    @10
    @10
    uniprg
    syl2anbr
    fveq2d
    fveq2d
    @2
    @3
    @10
    wss
    #
    @9
    @6
    wceq
    @0
    @11
    @12
    @15
    @1
    @13
    @14
    cA
    cB
    @10
    prssi
    syl2anbr
    @3
    hsupval
    syl
    cA
    cB
    sshjval
    3eqtr4rd
end
