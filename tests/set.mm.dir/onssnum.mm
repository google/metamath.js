include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "csuc.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "word.mm"
include "uniexg.mm"
include "ssorduni.mm"
include "elong.mm"
include "biimpar.mm"
include "syl2an.mm"
include "suceloni.mm"
include "onenon.mm"
include "3syl.mm"
include "onsucuni.mm"
include "adantl.mm"
include "ssnum.mm"
include "syl2anc.mm"

theorem onssnum
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ A C_ On ) -> A e. dom card )

  proof
    cA
    cV
    wcel
    #
    cA
    con0
    wss
    #
    wa
    #
    cA
    cuni
    #
    csuc
    #
    ccrd
    cdm
    #
    wcel
    #
    cA
    @4
    wss
    #
    cA
    @5
    wcel
    @2
    @3
    con0
    wcel
    #
    @4
    con0
    wcel
    @6
    @0
    @3
    cvv
    wcel
    #
    @3
    word
    #
    @8
    @1
    cA
    cV
    uniexg
    cA
    ssorduni
    @9
    @8
    @10
    @3
    cvv
    elong
    biimpar
    syl2an
    @3
    suceloni
    @4
    onenon
    3syl
    @1
    @7
    @0
    cA
    onsucuni
    adantl
    @4
    cA
    ssnum
    syl2anc
end
