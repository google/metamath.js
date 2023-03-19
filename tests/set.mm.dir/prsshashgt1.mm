include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cvv.mm"
include "elex.mm"
include "id.mm"
include "hashprb.mm"
include "biimpi.mm"
include "syl3an.mm"
include "ad2antrr.mm"
include "hashss.mm"
include "adantll.mm"
include "eqbrtrrd.mm"
include "ex.mm"

theorem prsshashgt1
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let cW: class W


  assert |- ( ( ( A e. V /\ B e. W /\ A =/= B ) /\ C e. U ) -> ( { A , B } C_ C -> 2 <_ ( # ` C ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cC
    cU
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    cC
    wss
    #
    c2
    cC
    chash
    cfv
    #
    cle
    wbr
    @5
    @7
    wa
    @6
    chash
    cfv
    #
    c2
    @8
    cle
    @3
    @9
    c2
    wceq
    #
    @4
    @7
    @0
    cA
    cvv
    wcel
    #
    @1
    cB
    cvv
    wcel
    #
    @2
    @2
    @10
    cA
    cV
    elex
    cB
    cW
    elex
    @2
    id
    @11
    @12
    @2
    w3a
    @10
    cA
    cB
    hashprb
    biimpi
    syl3an
    ad2antrr
    @4
    @7
    @9
    @8
    cle
    wbr
    @3
    cC
    @6
    cU
    hashss
    adantll
    eqbrtrrd
    ex
end
