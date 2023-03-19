include "whe.mm"
include "wa.mm"
include "cun.mm"
include "cima.mm"
include "wss.mm"
include "df-he.mm"
include "imaundir.mm"
include "unss.mm"
include "biimpi.mm"
include "syl5eqss.mm"
include "syl2anb.mm"
include "sylibr.mm"

theorem unhe1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( ( R hereditary A /\ S hereditary A ) -> ( R u. S ) hereditary A )

  proof
    cA
    cR
    whe
    #
    cA
    cS
    whe
    #
    wa
    cR
    cS
    cun
    #
    cA
    cima
    #
    cA
    wss
    #
    cA
    @2
    whe
    @0
    cR
    cA
    cima
    #
    cA
    wss
    #
    cS
    cA
    cima
    #
    cA
    wss
    #
    @4
    @1
    cA
    cR
    df-he
    cA
    cS
    df-he
    @6
    @8
    wa
    #
    @3
    @5
    @7
    cun
    #
    cA
    cR
    cS
    cA
    imaundir
    @9
    @10
    cA
    wss
    @5
    @7
    cA
    unss
    biimpi
    syl5eqss
    syl2anb
    cA
    @2
    df-he
    sylibr
end
