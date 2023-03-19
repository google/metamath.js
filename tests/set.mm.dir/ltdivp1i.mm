include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "clt.mm"
include "w3a.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "1re.mm"
include "readdcli.mm"
include "ltp1i.mm"
include "ltleii.mm"
include "lemul2a.mm"
include "mpan2.mm"
include "mp3an12.mm"
include "mpan.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "0re.mm"
include "lelttri.mm"
include "wb.mm"
include "wne.mm"
include "gt0ne0i.mm"
include "redivclzi.mm"
include "syl.mm"
include "ltmul1.mm"
include "mp3an1.mm"
include "mpanr1.mm"
include "mpancom.mm"
include "biimpd.mm"
include "imp.mm"
include "wceq.mm"
include "recni.mm"
include "divcan1zi.mm"
include "3syl.mm"
include "adantr.mm"
include "breqtrd.mm"
include "3adant1.mm"
include "remulcli.mm"
include "syl2anc.mm"

theorem ltdivp1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR
  assume ltmul1.3: |- C e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ C /\ A < ( B / ( C + 1 ) ) ) -> ( A x. C ) < B )

  proof
    cc0
    cA
    cle
    wbr
    #
    cc0
    cC
    cle
    wbr
    #
    cA
    cB
    cC
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    w3a
    cA
    cC
    cmul
    co
    #
    cA
    @2
    cmul
    co
    #
    cle
    wbr
    #
    @6
    cB
    clt
    wbr
    #
    @5
    cB
    clt
    wbr
    @0
    @1
    @7
    @4
    cA
    cr
    wcel
    #
    @0
    @7
    ltplus1.1
    cC
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @9
    @0
    wa
    #
    @7
    ltmul1.3
    cC
    c1
    ltmul1.3
    1re
    readdcli
    #
    @10
    @11
    @12
    w3a
    cC
    @2
    cle
    wbr
    @7
    cC
    @2
    ltmul1.3
    @13
    cC
    ltmul1.3
    ltp1i
    #
    ltleii
    cC
    @2
    cA
    lemul2a
    mpan2
    mp3an12
    mpan
    3ad2ant1
    @1
    @4
    @8
    @0
    @1
    @4
    wa
    @6
    @3
    @2
    cmul
    co
    #
    cB
    clt
    @1
    @4
    @6
    @15
    clt
    wbr
    #
    @1
    cc0
    @2
    clt
    wbr
    #
    @4
    @16
    wi
    @1
    cC
    @2
    clt
    wbr
    @17
    @14
    cc0
    cC
    @2
    0re
    ltmul1.3
    @13
    lelttri
    mpan2
    #
    @17
    @4
    @16
    @3
    cr
    wcel
    #
    @17
    @4
    @16
    wb
    #
    @17
    @2
    cc0
    wne
    #
    @19
    @2
    @13
    gt0ne0i
    #
    cB
    @2
    prodgt0.2
    @13
    redivclzi
    syl
    @19
    @11
    @17
    @20
    @13
    @9
    @19
    @11
    @17
    wa
    @20
    ltplus1.1
    cA
    @3
    @2
    ltmul1
    mp3an1
    mpanr1
    mpancom
    biimpd
    syl
    imp
    @1
    @15
    cB
    wceq
    #
    @4
    @1
    @17
    @21
    @23
    @18
    @22
    cB
    @2
    cB
    prodgt0.2
    recni
    @2
    @13
    recni
    divcan1zi
    3syl
    adantr
    breqtrd
    3adant1
    @5
    @6
    cB
    cA
    cC
    ltplus1.1
    ltmul1.3
    remulcli
    cA
    @2
    ltplus1.1
    @13
    remulcli
    prodgt0.2
    lelttri
    syl2anc
end
