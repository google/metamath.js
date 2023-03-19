include "ctrans.mm"
include "wcel.mm"
include "cvv.mm"
include "cep.mm"
include "ccom.mm"
include "cdif.mm"
include "crn.mm"
include "wtr.mm"
include "df-trans.mm"
include "eleq2i.mm"
include "dftr6.mm"
include "bitr4i.mm"

theorem eltrans
  let cA: class A
  assume eltrans.1: |- A e. _V


  assert |- ( A e. Trans <-> Tr A )

  proof
    cA
    ctrans
    wcel
    cA
    cvv
    cep
    cep
    ccom
    cep
    cdif
    crn
    cdif
    #
    wcel
    cA
    wtr
    ctrans
    @0
    cA
    df-trans
    eleq2i
    cA
    eltrans.1
    dftr6
    bitr4i
end
