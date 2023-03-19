include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "cr.mm"
include "wa.mm"
include "elunitrn.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "redivcld.mm"
include "adantr.mm"
include "clt.mm"
include "elunitge0.mm"
include "wb.mm"
include "0re.mm"
include "ltlen.mm"
include "sylancr.mm"
include "biimpar.mm"
include "3impb.mm"
include "3com23.mm"
include "mpd3an3.mm"
include "3adant1.mm"
include "divge0.mm"
include "syl22anc.mm"
include "cmul.mm"
include "1red.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "ax-1rid.mm"
include "breq2d.mm"
include "syl.mm"
include "bitr2d.mm"
include "biimpa.mm"
include "3jca.mm"
include "ex.mm"
include "syl5ibr.mm"
include "impbid.mm"
include "1re.mm"
include "elicc2i.mm"
include "syl6bbr.mm"

theorem unitdivcld
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( 0 [,] 1 ) /\ B e. ( 0 [,] 1 ) /\ B =/= 0 ) -> ( A <_ B <-> ( A / B ) e. ( 0 [,] 1 ) ) )

  proof
    cA
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cdiv
    co
    #
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    w3a
    #
    @6
    @0
    wcel
    @4
    @5
    @10
    @4
    @5
    @10
    @4
    @5
    wa
    @7
    @8
    @9
    @4
    @7
    @5
    @4
    cA
    cB
    @1
    @2
    cA
    cr
    wcel
    #
    @3
    cA
    elunitrn
    3ad2ant1
    #
    @2
    @1
    cB
    cr
    wcel
    #
    @3
    cB
    elunitrn
    #
    3ad2ant2
    #
    @1
    @2
    @3
    simp3
    redivcld
    adantr
    @4
    @8
    @5
    @4
    @11
    cc0
    cA
    cle
    wbr
    #
    @13
    cc0
    cB
    clt
    wbr
    #
    @8
    @12
    @1
    @2
    @16
    @3
    cA
    elunitge0
    3ad2ant1
    @15
    @2
    @3
    @17
    @1
    @2
    @3
    cc0
    cB
    cle
    wbr
    #
    @17
    @2
    @18
    @3
    cB
    elunitge0
    adantr
    @2
    @18
    @3
    @17
    @2
    @18
    @3
    @17
    @2
    @17
    @18
    @3
    wa
    #
    @2
    cc0
    cr
    wcel
    @13
    @17
    @19
    wb
    0re
    @14
    cc0
    cB
    ltlen
    sylancr
    biimpar
    3impb
    3com23
    mpd3an3
    3adant1
    #
    cA
    cB
    divge0
    syl22anc
    adantr
    @4
    @5
    @9
    @4
    @9
    cA
    cB
    c1
    cmul
    co
    #
    cle
    wbr
    #
    @5
    @4
    @11
    c1
    cr
    wcel
    @13
    @17
    @9
    @22
    wb
    @12
    @4
    1red
    @15
    @20
    cA
    c1
    cB
    ledivmul
    syl112anc
    @4
    @13
    @22
    @5
    wb
    @15
    @13
    @21
    cB
    cA
    cle
    cB
    ax-1rid
    breq2d
    syl
    bitr2d
    #
    biimpa
    3jca
    ex
    @10
    @5
    @4
    @9
    @7
    @8
    @9
    simp3
    @23
    syl5ibr
    impbid
    cc0
    c1
    @6
    0re
    1re
    elicc2i
    syl6bbr
end
