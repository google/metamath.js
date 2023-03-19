include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "c3.mm"
include "c5.mm"
include "cun.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "cz.mm"
include "nnz.mm"
include "lgsdir2lem3.mm"
include "sylan.mm"
include "wo.mm"
include "wi.mm"
include "elun.mm"
include "ovex.mm"
include "elpr.mm"
include "2lgslem3a1.mm"
include "a1d.mm"
include "expcom.mm"
include "impd.mm"
include "2lgslem3d1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"
include "iftrue.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "ex.mm"
include "2lgslem3b1.mm"
include "2lgslem3c1.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "nesymi.mm"
include "3re.mm"
include "3lt7.mm"
include "neii.mm"
include "pm3.2i.mm"
include "eqeq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "mpbiri.mm"
include "1lt5.mm"
include "5re.mm"
include "5lt7.mm"
include "ioran.mm"
include "xchnxbir.mm"
include "sylibr.mm"
include "iffalsed.mm"
include "expimpd.mm"
include "mpcom.mm"

theorem 2lgslem3
  let cP: class P
  let cN: class N
  let vk: setvar k
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( P e. NN /\ -. 2 || P ) -> ( N mod 2 ) = if ( ( P mod 8 ) e. { 1 , 7 } , 0 , 1 ) )

  proof
    cP
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    c3
    c5
    cpr
    #
    cun
    wcel
    #
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    cN
    c2
    cmo
    co
    #
    @0
    @1
    wcel
    #
    cc0
    c1
    cif
    #
    wceq
    #
    @4
    cP
    cz
    wcel
    @5
    @3
    cP
    nnz
    cP
    lgsdir2lem3
    sylan
    @3
    @8
    @0
    @2
    wcel
    #
    wo
    @6
    @10
    wi
    #
    @0
    @1
    @2
    elun
    @8
    @12
    @11
    @8
    @6
    @10
    @8
    @6
    wa
    @7
    cc0
    @9
    @8
    @6
    @7
    cc0
    wceq
    #
    @8
    @0
    c1
    wceq
    #
    @0
    c7
    wceq
    #
    wo
    #
    @6
    @13
    wi
    #
    @0
    c1
    c7
    cP
    c8
    cmo
    ovex
    #
    elpr
    #
    @14
    @17
    @15
    @14
    @4
    @5
    @13
    @4
    @14
    @5
    @13
    wi
    #
    @4
    @14
    wa
    @13
    @5
    cP
    cN
    2lgslem2.n
    2lgslem3a1
    a1d
    expcom
    impd
    @15
    @4
    @5
    @13
    @4
    @15
    @20
    @4
    @15
    wa
    @13
    @5
    cP
    cN
    2lgslem2.n
    2lgslem3d1
    a1d
    expcom
    impd
    jaoi
    sylbi
    imp
    @8
    @9
    cc0
    wceq
    @6
    @8
    cc0
    c1
    iftrue
    adantr
    eqtr4d
    ex
    @11
    @0
    c3
    wceq
    #
    @0
    c5
    wceq
    #
    wo
    #
    @12
    @0
    c3
    c5
    @18
    elpr
    @23
    @4
    @5
    @10
    @23
    @4
    wa
    #
    @10
    @5
    @24
    @7
    c1
    @9
    @23
    @4
    @7
    c1
    wceq
    #
    @21
    @4
    @25
    wi
    @22
    @4
    @21
    @25
    cP
    cN
    2lgslem2.n
    2lgslem3b1
    expcom
    @4
    @22
    @25
    cP
    cN
    2lgslem2.n
    2lgslem3c1
    expcom
    jaoi
    imp
    @24
    @8
    cc0
    c1
    @24
    @14
    wn
    #
    @15
    wn
    #
    wa
    #
    @8
    wn
    @23
    @28
    @4
    @21
    @28
    @22
    @21
    @28
    c3
    c1
    wceq
    #
    wn
    #
    c3
    c7
    wceq
    #
    wn
    #
    wa
    @30
    @32
    c1
    c3
    c1
    c3
    1re
    1lt3
    ltneii
    nesymi
    c3
    c7
    c3
    c7
    3re
    3lt7
    ltneii
    neii
    pm3.2i
    @21
    @26
    @30
    @27
    @32
    @21
    @14
    @29
    @0
    c3
    c1
    eqeq1
    notbid
    @21
    @15
    @31
    @0
    c3
    c7
    eqeq1
    notbid
    anbi12d
    mpbiri
    @22
    @28
    c5
    c1
    wceq
    #
    wn
    #
    c5
    c7
    wceq
    #
    wn
    #
    wa
    @34
    @36
    c1
    c5
    c1
    c5
    1re
    1lt5
    ltneii
    nesymi
    c5
    c7
    c5
    c7
    5re
    5lt7
    ltneii
    neii
    pm3.2i
    @22
    @26
    @34
    @27
    @36
    @22
    @14
    @33
    @0
    c5
    c1
    eqeq1
    notbid
    @22
    @15
    @35
    @0
    c5
    c7
    eqeq1
    notbid
    anbi12d
    mpbiri
    jaoi
    adantr
    @16
    @28
    @8
    @14
    @15
    ioran
    @19
    xchnxbir
    sylibr
    iffalsed
    eqtr4d
    a1d
    expimpd
    sylbi
    jaoi
    sylbi
    mpcom
end
