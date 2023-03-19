include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "cun.mm"
include "elmapi.mm"
include "id.mm"
include "fresaunres2.mm"
include "syl3an.mm"

theorem elmapresaunres2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G )

  proof
    cF
    cC
    cA
    cmap
    co
    wcel
    cA
    cC
    cF
    wf
    cG
    cC
    cB
    cmap
    co
    wcel
    cB
    cC
    cG
    wf
    cF
    cA
    cB
    cin
    #
    cres
    cG
    @0
    cres
    wceq
    #
    @1
    cF
    cG
    cun
    cB
    cres
    cG
    wceq
    cF
    cC
    cA
    elmapi
    cG
    cC
    cB
    elmapi
    @1
    id
    cA
    cB
    cC
    cF
    cG
    fresaunres2
    syl3an
end
