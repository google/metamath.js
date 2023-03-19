include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "fzolb.mm"
include "df-3an.mm"
include "bitri.mm"
include "baib.mm"

theorem fzolb2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M e. ( M ..^ N ) <-> M < N ) )

  proof
    cM
    cM
    cN
    cfzo
    co
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    clt
    wbr
    #
    @0
    @1
    @2
    @4
    w3a
    @3
    @4
    wa
    cM
    cN
    fzolb
    @1
    @2
    @4
    df-3an
    bitri
    baib
end
