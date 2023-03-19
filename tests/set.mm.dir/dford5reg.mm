include "word.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "wa.mm"
include "wor.mm"
include "df-ord.mm"
include "wfr.mm"
include "zfregfr.mm"
include "df-we.mm"
include "mpbiran.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dford5reg
  let cA: class A


  assert |- ( Ord A <-> ( Tr A /\ _E Or A ) )

  proof
    cA
    word
    cA
    wtr
    #
    cA
    cep
    wwe
    #
    wa
    @0
    cA
    cep
    wor
    #
    wa
    cA
    df-ord
    @1
    @2
    @0
    @1
    cA
    cep
    wfr
    @2
    cA
    zfregfr
    cA
    cep
    df-we
    mpbiran
    anbi2i
    bitri
end
