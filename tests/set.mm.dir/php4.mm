include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "wpss.mm"
include "csdm.mm"
include "wbr.mm"
include "sucidg.mm"
include "word.mm"
include "wa.mm"
include "wb.mm"
include "nnord.mm"
include "ordsuc.mm"
include "biimpi.mm"
include "ancli.mm"
include "ordelpss.mm"
include "3syl.mm"
include "mpbid.mm"
include "peano2b.mm"
include "php2.mm"
include "sylanb.mm"
include "mpdan.mm"

theorem php4
  let cA: class A


  assert |- ( A e. _om -> A ~< suc A )

  proof
    cA
    com
    wcel
    #
    cA
    cA
    csuc
    #
    wpss
    #
    cA
    @1
    csdm
    wbr
    #
    @0
    cA
    @1
    wcel
    #
    @2
    cA
    com
    sucidg
    @0
    cA
    word
    #
    @5
    @1
    word
    #
    wa
    @4
    @2
    wb
    cA
    nnord
    @5
    @6
    @5
    @6
    cA
    ordsuc
    biimpi
    ancli
    cA
    @1
    ordelpss
    3syl
    mpbid
    @0
    @1
    com
    wcel
    @2
    @3
    cA
    peano2b
    @1
    cA
    php2
    sylanb
    mpdan
end
