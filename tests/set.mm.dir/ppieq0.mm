include "cr.mm"
include "wcel.mm"
include "cppi.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "wne.mm"
include "wb.mm"
include "2re.mm"
include "lenlt.mm"
include "mpan.mm"
include "wa.mm"
include "ppinncl.mm"
include "nnne0d.mm"
include "ex.mm"
include "sylbird.mm"
include "necon4bd.mm"
include "cfl.mm"
include "c1.mm"
include "reflcl.mm"
include "adantr.mm"
include "1red.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "2z.mm"
include "fllt.mm"
include "mpan2.mm"
include "biimpa.mm"
include "df-2.mm"
include "syl6breq.mm"
include "flcl.mm"
include "1z.mm"
include "zleltp1.mm"
include "sylancl.mm"
include "mpbird.mm"
include "ppiwordi.mm"
include "syl3anc.mm"
include "ppifl.mm"
include "ppi1.mm"
include "a1i.mm"
include "3brtr3d.mm"
include "cn0.mm"
include "ppicl.mm"
include "nn0le0eq0.mm"
include "syl.mm"
include "mpbid.mm"
include "impbid.mm"

theorem ppieq0
  let cA: class A


  assert |- ( A e. RR -> ( ( ppi ` A ) = 0 <-> A < 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cppi
    cfv
    #
    cc0
    wceq
    #
    cA
    c2
    clt
    wbr
    #
    @0
    @3
    @1
    cc0
    @0
    @3
    wn
    #
    c2
    cA
    cle
    wbr
    #
    @1
    cc0
    wne
    #
    c2
    cr
    wcel
    @0
    @5
    @4
    wb
    2re
    c2
    cA
    lenlt
    mpan
    @0
    @5
    @6
    @0
    @5
    wa
    @1
    cA
    ppinncl
    nnne0d
    ex
    sylbird
    necon4bd
    @0
    @3
    @2
    @0
    @3
    wa
    #
    @1
    cc0
    cle
    wbr
    #
    @2
    @7
    cA
    cfl
    cfv
    #
    cppi
    cfv
    #
    c1
    cppi
    cfv
    #
    @1
    cc0
    cle
    @7
    @9
    cr
    wcel
    #
    c1
    cr
    wcel
    @9
    c1
    cle
    wbr
    #
    @10
    @11
    cle
    wbr
    @0
    @12
    @3
    cA
    reflcl
    adantr
    @7
    1red
    @7
    @13
    @9
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @7
    @9
    c2
    @14
    clt
    @0
    @3
    @9
    c2
    clt
    wbr
    #
    @0
    c2
    cz
    wcel
    @3
    @16
    wb
    2z
    cA
    c2
    fllt
    mpan2
    biimpa
    df-2
    syl6breq
    @7
    @9
    cz
    wcel
    #
    c1
    cz
    wcel
    @13
    @15
    wb
    @0
    @17
    @3
    cA
    flcl
    adantr
    1z
    @9
    c1
    zleltp1
    sylancl
    mpbird
    @9
    c1
    ppiwordi
    syl3anc
    @0
    @10
    @1
    wceq
    @3
    cA
    ppifl
    adantr
    @11
    cc0
    wceq
    @7
    ppi1
    a1i
    3brtr3d
    @7
    @1
    cn0
    wcel
    #
    @8
    @2
    wb
    @0
    @18
    @3
    cA
    ppicl
    adantr
    @1
    nn0le0eq0
    syl
    mpbid
    ex
    impbid
end
