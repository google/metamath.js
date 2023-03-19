include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "cle.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nn0re.mm"
include "adantr.mm"
include "ltnle.mm"
include "sylancr.mm"
include "nn0le0eq0.mm"
include "notbid.mm"
include "bitrd.mm"
include "df-ne.mm"
include "syl6bbr.mm"
include "anbi2d.mm"
include "nne.mm"
include "breq1.mm"
include "sylbi.mm"
include "biimpar.mm"
include "syl6bir.mm"
include "expd.mm"
include "ax-1.mm"
include "jctir.mm"
include "jaob.mm"
include "sylibr.mm"
include "syl5bi.mm"
include "nn0ge0.mm"
include "adantl.mm"
include "lelttr.mm"
include "mp3an1.mm"
include "syl2anr.mm"
include "mpand.mm"
include "sylibd.mm"
include "imim2d.mm"
include "jcad.mm"
include "pm3.34.mm"
include "impbid1.mm"
include "con34b.mm"
include "imbi12i.mm"
include "bitr4i.mm"
include "anbi2i.mm"

theorem algcvgblem
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( ( N =/= 0 -> N < M ) <-> ( ( M =/= 0 -> N < M ) /\ ( M = 0 -> N = 0 ) ) ) )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cc0
    wne
    #
    cN
    cM
    clt
    wbr
    #
    wi
    #
    cM
    cc0
    wne
    #
    @4
    wi
    #
    @3
    @6
    wi
    #
    wa
    #
    @7
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wi
    #
    wa
    @2
    @5
    @9
    @2
    @5
    @7
    @8
    @5
    @3
    wn
    #
    @4
    wo
    #
    @2
    @7
    @3
    @4
    imor
    @2
    @13
    @7
    wi
    #
    @4
    @7
    wi
    #
    wa
    @14
    @7
    wi
    @2
    @15
    @16
    @2
    @13
    @6
    @4
    @2
    @13
    @6
    wa
    @13
    cc0
    cM
    clt
    wbr
    #
    wa
    @4
    @2
    @17
    @6
    @13
    @2
    @17
    @10
    wn
    #
    @6
    @2
    @17
    cM
    cc0
    cle
    wbr
    #
    wn
    #
    @18
    @2
    cc0
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @17
    @20
    wb
    0re
    @0
    @22
    @1
    cM
    nn0re
    #
    adantr
    cc0
    cM
    ltnle
    sylancr
    @0
    @20
    @18
    wb
    @1
    @0
    @19
    @10
    cM
    nn0le0eq0
    notbid
    adantr
    bitrd
    cM
    cc0
    df-ne
    #
    syl6bbr
    #
    anbi2d
    @13
    @4
    @17
    @13
    @11
    @4
    @17
    wb
    cN
    cc0
    nne
    cN
    cc0
    cM
    clt
    breq1
    sylbi
    biimpar
    syl6bir
    expd
    @4
    @6
    ax-1
    jctir
    @13
    @7
    @4
    jaob
    sylibr
    syl5bi
    @2
    @4
    @6
    @3
    @2
    @4
    @17
    @6
    @2
    cc0
    cN
    cle
    wbr
    #
    @4
    @17
    @1
    @26
    @0
    cN
    nn0ge0
    adantl
    @1
    cN
    cr
    wcel
    #
    @22
    @26
    @4
    wa
    @17
    wi
    #
    @0
    cN
    nn0re
    @23
    @21
    @27
    @22
    @28
    0re
    cc0
    cN
    cM
    lelttr
    mp3an1
    syl2anr
    mpand
    @25
    sylibd
    imim2d
    jcad
    @3
    @6
    @4
    pm3.34
    impbid1
    @12
    @8
    @7
    @12
    @11
    wn
    #
    @18
    wi
    @8
    @10
    @11
    con34b
    @3
    @29
    @6
    @18
    cN
    cc0
    df-ne
    @24
    imbi12i
    bitr4i
    anbi2i
    syl6bbr
end
