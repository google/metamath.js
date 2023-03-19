include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "ax-his1.mm"
include "fveq2d.mm"
include "cc.mm"
include "hicl.mm"
include "ancoms.mm"
include "abscjd.mm"
include "eqtrd.mm"

theorem abshicom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( abs ` ( A .ih B ) ) = ( abs ` ( B .ih A ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csp
    co
    #
    cabs
    cfv
    cB
    cA
    csp
    co
    #
    ccj
    cfv
    #
    cabs
    cfv
    @4
    cabs
    cfv
    @2
    @3
    @5
    cabs
    cA
    cB
    ax-his1
    fveq2d
    @2
    @4
    @1
    @0
    @4
    cc
    wcel
    cB
    cA
    hicl
    ancoms
    abscjd
    eqtrd
end
