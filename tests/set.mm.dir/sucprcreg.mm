include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "wceq.mm"
include "sucprc.mm"
include "wa.mm"
include "elirr.mm"
include "csn.mm"
include "wss.mm"
include "cun.mm"
include "df-suc.mm"
include "eqeq1i.mm"
include "ssequn2.mm"
include "bitr4i.mm"
include "biimpi.mm"
include "snidg.mm"
include "ssel2.mm"
include "syl2an.mm"
include "mto.mm"
include "imnani.mm"
include "impbii.mm"

theorem sucprcreg
  let cA: class A


  assert |- ( -. A e. _V <-> suc A = A )

  proof
    cA
    cvv
    wcel
    #
    wn
    cA
    csuc
    #
    cA
    wceq
    #
    cA
    sucprc
    @2
    @0
    @2
    @0
    wa
    cA
    cA
    wcel
    #
    cA
    elirr
    @2
    cA
    csn
    #
    cA
    wss
    #
    cA
    @4
    wcel
    @3
    @0
    @2
    @5
    @2
    cA
    @4
    cun
    #
    cA
    wceq
    @5
    @1
    @6
    cA
    cA
    df-suc
    eqeq1i
    @4
    cA
    ssequn2
    bitr4i
    biimpi
    cA
    cvv
    snidg
    @4
    cA
    cA
    ssel2
    syl2an
    mto
    imnani
    impbii
end
