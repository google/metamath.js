include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "word.mm"
include "csuc.mm"
include "ssorduni.mm"
include "wa.mm"
include "ssid.mm"
include "ordunisssuc.mm"
include "mpbii.mm"
include "mpdan.mm"

theorem onsucuni
  let cA: class A


  assert |- ( A C_ On -> A C_ suc U. A )

  proof
    cA
    con0
    wss
    #
    cA
    cuni
    #
    word
    #
    cA
    @1
    csuc
    wss
    #
    cA
    ssorduni
    @0
    @2
    wa
    @1
    @1
    wss
    @3
    @1
    ssid
    cA
    @1
    ordunisssuc
    mpbii
    mpdan
end
