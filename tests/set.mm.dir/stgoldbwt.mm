include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbo.mm"
include "wcel.mm"
include "wi.mm"
include "c5.mm"
include "cgbow.mm"
include "codd.mm"
include "wa.mm"
include "pm3.35.mm"
include "gbogbow.mm"
include "a1d.mm"
include "syl.mm"
include "ex.mm"
include "wn.mm"
include "cle.mm"
include "oddz.mm"
include "zred.mm"
include "cr.mm"
include "7re.mm"
include "a1i.mm"
include "lenltd.mm"
include "c6.mm"
include "wceq.mm"
include "wo.mm"
include "leloed.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "adantr.mm"
include "6nn.mm"
include "nnzi.mm"
include "jctir.mm"
include "adantl.mm"
include "df-7.mm"
include "breq2i.mm"
include "biimpi.mm"
include "df-6.mm"
include "wb.mm"
include "5nn.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "biimpa.mm"
include "syl5eqbr.mm"
include "anim12ci.mm"
include "zgeltp1eq.mm"
include "sylc.mm"
include "orcd.mm"
include "olc.mm"
include "jaoi.mm"
include "expd.mm"
include "com12.mm"
include "sylbid.mm"
include "eleq1.mm"
include "ceven.mm"
include "6even.mm"
include "evennodd.mm"
include "pm2.21d.mm"
include "mp1i.mm"
include "7gbow.mm"
include "mpbiri.mm"
include "syl6d.mm"
include "sylbird.mm"
include "a1dd.mm"
include "pm2.61i.mm"
include "ralimia.mm"

theorem stgoldbwt
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( A. n e. Odd ( 7 < n -> n e. GoldbachOdd ) -> A. n e. Odd ( 5 < n -> n e. GoldbachOddW ) )

  proof
    c7
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cgbo
    wcel
    #
    wi
    #
    c5
    @0
    clt
    wbr
    #
    @0
    cgbow
    wcel
    #
    wi
    #
    vn
    codd
    @1
    @0
    codd
    wcel
    #
    @3
    @6
    wi
    #
    wi
    @1
    @8
    @7
    @1
    @3
    @6
    @1
    @3
    wa
    @2
    @6
    @1
    @2
    pm3.35
    @2
    @5
    @4
    @0
    gbogbow
    a1d
    syl
    ex
    a1d
    @1
    wn
    #
    @7
    @6
    @3
    @7
    @9
    @6
    @7
    @9
    @0
    c7
    cle
    wbr
    #
    @6
    @7
    @0
    c7
    @7
    @0
    @0
    oddz
    #
    zred
    #
    c7
    cr
    wcel
    @7
    7re
    a1i
    #
    lenltd
    @7
    @10
    @4
    @0
    c6
    wceq
    #
    @0
    c7
    wceq
    #
    wo
    #
    @5
    @7
    @10
    @0
    c7
    clt
    wbr
    #
    @15
    wo
    #
    @4
    @16
    wi
    #
    @7
    @0
    c7
    @12
    @13
    leloed
    @18
    @7
    @19
    @18
    @7
    @4
    @16
    @17
    @7
    @4
    wa
    #
    @16
    wi
    @15
    @17
    @20
    @16
    @17
    @20
    wa
    #
    @14
    @15
    @21
    @0
    cz
    wcel
    #
    c6
    cz
    wcel
    #
    wa
    #
    c6
    @0
    cle
    wbr
    #
    @0
    c6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    @14
    @20
    @24
    @17
    @20
    @22
    @23
    @7
    @22
    @4
    @11
    adantr
    c6
    6nn
    nnzi
    jctir
    adantl
    @17
    @27
    @20
    @25
    @17
    @27
    c7
    @26
    @0
    clt
    df-7
    breq2i
    biimpi
    @20
    c6
    c5
    c1
    caddc
    co
    #
    @0
    cle
    df-6
    @7
    @4
    @28
    @0
    cle
    wbr
    #
    @7
    c5
    cz
    wcel
    @22
    @4
    @29
    wb
    c5
    5nn
    nnzi
    @11
    c5
    @0
    zltp1le
    sylancr
    biimpa
    syl5eqbr
    anim12ci
    c6
    @0
    zgeltp1eq
    sylc
    orcd
    ex
    @15
    @16
    @20
    @15
    @14
    olc
    a1d
    jaoi
    expd
    com12
    sylbid
    @16
    @7
    @5
    @14
    @7
    @5
    wi
    @15
    @14
    @7
    c6
    codd
    wcel
    #
    @5
    @0
    c6
    codd
    eleq1
    c6
    ceven
    wcel
    #
    @30
    @5
    wi
    @14
    6even
    @31
    @30
    @5
    c6
    evennodd
    pm2.21d
    mp1i
    sylbid
    @15
    @5
    @7
    @15
    @5
    c7
    cgbow
    wcel
    7gbow
    @0
    c7
    cgbow
    eleq1
    mpbiri
    a1d
    jaoi
    com12
    syl6d
    sylbird
    com12
    a1dd
    pm2.61i
    ralimia
end
