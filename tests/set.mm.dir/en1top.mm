include "ctop.mm"
include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "wceq.mm"
include "wi.mm"
include "0opn.mm"
include "en1eqsn.mm"
include "ex.mm"
include "syl.mm"
include "id.mm"
include "0ex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "impbid1.mm"

theorem en1top
  let cJ: class J


  assert |- ( J e. Top -> ( J ~~ 1o <-> J = { (/) } ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    c1o
    cen
    wbr
    #
    cJ
    c0
    csn
    #
    wceq
    #
    @0
    c0
    cJ
    wcel
    #
    @1
    @3
    wi
    cJ
    0opn
    @4
    @1
    @3
    c0
    cJ
    en1eqsn
    ex
    syl
    @3
    cJ
    @2
    c1o
    cen
    @3
    id
    c0
    0ex
    ensn1
    syl6eqbr
    impbid1
end
