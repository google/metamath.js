include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "wf.mm"
include "elmapi.mm"
include "id.mm"
include "fresaun.mm"
include "syl3an.mm"
include "cvv.mm"
include "elmapex.mm"
include "simpld.mm"
include "3ad2ant1.mm"
include "simprd.mm"
include "unexg.mm"
include "syl2an.mm"
include "3adant3.mm"
include "elmapd.mm"
include "mpbird.mm"

theorem elmapresaun
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( C ^m A ) /\ G e. ( C ^m B ) /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) e. ( C ^m ( A u. B ) ) )

  proof
    cF
    cC
    cA
    cmap
    co
    wcel
    #
    cG
    cC
    cB
    cmap
    co
    wcel
    #
    cF
    cA
    cB
    cin
    #
    cres
    cG
    @2
    cres
    wceq
    #
    w3a
    #
    cF
    cG
    cun
    #
    cC
    cA
    cB
    cun
    #
    cmap
    co
    wcel
    @6
    cC
    @5
    wf
    #
    @0
    cA
    cC
    cF
    wf
    @1
    cB
    cC
    cG
    wf
    @3
    @3
    @7
    cF
    cC
    cA
    elmapi
    cG
    cC
    cB
    elmapi
    @3
    id
    cA
    cB
    cC
    cF
    cG
    fresaun
    syl3an
    @4
    cC
    @6
    @5
    cvv
    cvv
    @0
    @1
    cC
    cvv
    wcel
    #
    @3
    @0
    @8
    cA
    cvv
    wcel
    #
    cF
    cC
    cA
    elmapex
    #
    simpld
    3ad2ant1
    @0
    @1
    @6
    cvv
    wcel
    #
    @3
    @0
    @9
    cB
    cvv
    wcel
    #
    @11
    @1
    @0
    @8
    @9
    @10
    simprd
    @1
    @8
    @12
    cG
    cC
    cB
    elmapex
    simprd
    cA
    cB
    cvv
    cvv
    unexg
    syl2an
    3adant3
    elmapd
    mpbird
end
