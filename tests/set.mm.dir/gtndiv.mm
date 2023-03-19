include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "wn.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "nngt0.mm"
include "wa.mm"
include "adantl.mm"
include "wi.mm"
include "0re.mm"
include "lttr.mm"
include "mp3an1.mm"
include "sylan.mm"
include "ancoms.mm"
include "mpand.mm"
include "3impia.mm"
include "divgt0d.mm"
include "simp3.mm"
include "cmul.mm"
include "wb.mm"
include "1re.mm"
include "ltdivmul2.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "recn.mm"
include "mulid2d.mm"
include "breq2d.mm"
include "3ad2ant1.mm"
include "bitrd.mm"
include "mpbird.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "0z.mm"
include "btwnnz.mm"
include "syl2anc.mm"

theorem gtndiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. NN /\ B < A ) -> -. ( B / A ) e. ZZ )

  proof
    cA
    cr
    wcel
    #
    cB
    cn
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    w3a
    #
    cc0
    cB
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    @4
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @4
    cz
    wcel
    wn
    #
    @3
    cB
    cA
    @1
    @0
    cB
    cr
    wcel
    #
    @2
    cB
    nnre
    #
    3ad2ant2
    #
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    cc0
    cB
    clt
    wbr
    #
    @2
    cB
    nngt0
    #
    3ad2ant2
    @0
    @1
    @2
    cc0
    cA
    clt
    wbr
    #
    @0
    @1
    wa
    @13
    @2
    @15
    @1
    @13
    @0
    @14
    adantl
    @1
    @0
    @13
    @2
    wa
    @15
    wi
    #
    @1
    @9
    @0
    @16
    @10
    cc0
    cr
    wcel
    @9
    @0
    @16
    0re
    cc0
    cB
    cA
    lttr
    mp3an1
    sylan
    ancoms
    mpand
    3impia
    #
    divgt0d
    @3
    @4
    c1
    @6
    clt
    @3
    @4
    c1
    clt
    wbr
    #
    @2
    @0
    @1
    @2
    simp3
    @3
    @18
    cB
    c1
    cA
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @3
    @9
    @0
    @15
    @18
    @20
    wb
    #
    @11
    @12
    @17
    @9
    c1
    cr
    wcel
    @0
    @15
    wa
    @21
    1re
    cB
    c1
    cA
    ltdivmul2
    mp3an2
    syl12anc
    @0
    @1
    @20
    @2
    wb
    @2
    @0
    @19
    cA
    cB
    clt
    @0
    cA
    cA
    recn
    mulid2d
    breq2d
    3ad2ant1
    bitrd
    mpbird
    0p1e1
    syl6breqr
    cc0
    cz
    wcel
    @5
    @7
    @8
    0z
    cc0
    @4
    btwnnz
    mp3an1
    syl2anc
end
