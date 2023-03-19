include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "wa.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "nn0n0n1ge2.mm"
include "3expib.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "ianor.mm"
include "nne.mm"
include "orbi12i.mm"
include "bitri.mm"
include "clt.mm"
include "wi.mm"
include "2pos.mm"
include "breq1.mm"
include "mpbiri.mm"
include "a1d.mm"
include "1lt2.mm"
include "jaoi.mm"
include "impcom.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "2re.mm"
include "jctir.mm"
include "adantr.mm"
include "ltnle.mm"
include "syl.mm"
include "mpbid.mm"
include "ex.mm"
include "syl5bi.mm"
include "impcon4bid.mm"

theorem nn0n0n1ge2b
  let cN: class N


  assert |- ( N e. NN0 -> ( ( N =/= 0 /\ N =/= 1 ) <-> 2 <_ N ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    wne
    #
    cN
    c1
    wne
    #
    wa
    #
    c2
    cN
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    cN
    nn0n0n1ge2
    3expib
    @3
    wn
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    wceq
    #
    wo
    #
    @0
    @4
    wn
    #
    @5
    @1
    wn
    #
    @2
    wn
    #
    wo
    @8
    @1
    @2
    ianor
    @10
    @6
    @11
    @7
    cN
    cc0
    nne
    cN
    c1
    nne
    orbi12i
    bitri
    @0
    @8
    @9
    @0
    @8
    wa
    #
    cN
    c2
    clt
    wbr
    #
    @9
    @8
    @0
    @13
    @6
    @0
    @13
    wi
    @7
    @6
    @13
    @0
    @6
    @13
    cc0
    c2
    clt
    wbr
    2pos
    cN
    cc0
    c2
    clt
    breq1
    mpbiri
    a1d
    @7
    @13
    @0
    @7
    @13
    c1
    c2
    clt
    wbr
    1lt2
    cN
    c1
    c2
    clt
    breq1
    mpbiri
    a1d
    jaoi
    impcom
    @12
    cN
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    wa
    #
    @13
    @9
    wb
    @0
    @16
    @8
    @0
    @14
    @15
    cN
    nn0re
    2re
    jctir
    adantr
    cN
    c2
    ltnle
    syl
    mpbid
    ex
    syl5bi
    impcon4bid
end
