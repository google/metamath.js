include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cres.mm"
include "wi.mm"
include "fvres.mm"
include "eqeq12d.mm"
include "biimprd.mm"
include "wn.mm"
include "c0.mm"
include "nfvres.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem fveqres
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F ` A ) = ( G ` A ) -> ( ( F |` B ) ` A ) = ( ( G |` B ) ` A ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    wceq
    #
    cA
    cF
    cB
    cres
    cfv
    #
    cA
    cG
    cB
    cres
    cfv
    #
    wceq
    #
    wi
    @0
    @6
    @3
    @0
    @4
    @1
    @5
    @2
    cA
    cB
    cF
    fvres
    cA
    cB
    cG
    fvres
    eqeq12d
    biimprd
    @0
    wn
    #
    @6
    @3
    @7
    @4
    c0
    @5
    cA
    cB
    cF
    nfvres
    cA
    cB
    cG
    nfvres
    eqtr4d
    a1d
    pm2.61i
end
