include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cts.mm"
include "cbs.mm"
include "ctps.mm"
include "c9.mm"
include "df-tset.mm"
include "1lt9.mm"
include "9nn.mm"
include "2strop.mm"
include "wceq.mm"
include "toponmax.mm"
include "2strbas.mm"
include "syl.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "ibi.mm"
include "eqid.mm"
include "tsettps.mm"

theorem eltpsg
  let cA: class A
  let cJ: class J
  let cK: class K
  assume eltpsi.k: |- K = { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , J >. }


  assert |- ( J e. ( TopOn ` A ) -> K e. TopSp )

  proof
    cJ
    cA
    ctopon
    cfv
    #
    wcel
    #
    cK
    cts
    cfv
    #
    cK
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    #
    cK
    ctps
    wcel
    @1
    @5
    @1
    cJ
    @2
    @0
    @4
    cA
    cJ
    cts
    cK
    c9
    @0
    eltpsi.k
    df-tset
    1lt9
    9nn
    2strop
    @1
    cA
    @3
    ctopon
    @1
    cA
    cJ
    wcel
    cA
    @3
    wceq
    cA
    cJ
    toponmax
    cA
    cJ
    cts
    cK
    c9
    cJ
    eltpsi.k
    df-tset
    1lt9
    9nn
    2strbas
    syl
    fveq2d
    eleq12d
    ibi
    @3
    @2
    cK
    @3
    eqid
    @2
    eqid
    tsettps
    syl
end
