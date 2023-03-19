include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "eltpi.mm"
include "fveq2.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "1le1.mm"
include "eqbrtri.mm"
include "syl6eqbr.mm"
include "abs0.mm"
include "0le1.mm"
include "3jaoi.mm"
include "syl.mm"
include "wa.mm"
include "zre.mm"
include "1red.mm"
include "absled.mm"
include "cr.mm"
include "cn.mm"
include "wi.mm"
include "elz.mm"
include "3mix2.mm"
include "a1d.mm"
include "nnle1eq1.mm"
include "biimpac.mm"
include "3mix3d.mm"
include "ex.mm"
include "adantl.mm"
include "com12.mm"
include "elnnz1.mm"
include "wb.mm"
include "lenegcon2.mm"
include "mpancom.mm"
include "neg1rr.mm"
include "a1i.mm"
include "id.mm"
include "letri3d.mm"
include "3mix1.mm"
include "eqcoms.mm"
include "syl6bir.mm"
include "adantr.mm"
include "com13.mm"
include "sylbid.mm"
include "impd.mm"
include "sylbi.mm"
include "imp.mm"
include "eltpg.mm"
include "mpbird.mm"
include "exp32.mm"
include "impcom.mm"
include "impbid2.mm"

theorem zabsle1
  let cZ: class Z


  assert |- ( Z e. ZZ -> ( Z e. { -u 1 , 0 , 1 } <-> ( abs ` Z ) <_ 1 ) )

  proof
    cZ
    cz
    wcel
    #
    cZ
    c1
    cneg
    #
    cc0
    c1
    ctp
    wcel
    #
    cZ
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @2
    cZ
    @1
    wceq
    #
    cZ
    cc0
    wceq
    #
    cZ
    c1
    wceq
    #
    w3o
    #
    @4
    cZ
    @1
    cc0
    c1
    eltpi
    @5
    @4
    @6
    @7
    @5
    @3
    @1
    cabs
    cfv
    #
    c1
    cle
    cZ
    @1
    cabs
    fveq2
    @9
    c1
    c1
    cle
    @9
    c1
    cabs
    cfv
    #
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    1le1
    eqbrtri
    syl6eqbr
    @6
    @3
    cc0
    cabs
    cfv
    #
    c1
    cle
    cZ
    cc0
    cabs
    fveq2
    @11
    cc0
    c1
    cle
    abs0
    0le1
    eqbrtri
    syl6eqbr
    @7
    @3
    @10
    c1
    cle
    cZ
    c1
    cabs
    fveq2
    @10
    c1
    c1
    cle
    abs1
    1le1
    eqbrtri
    syl6eqbr
    3jaoi
    syl
    @0
    @4
    @1
    cZ
    cle
    wbr
    #
    cZ
    c1
    cle
    wbr
    #
    wa
    #
    @2
    @0
    cZ
    c1
    cZ
    zre
    @0
    1red
    absled
    @0
    cZ
    cr
    wcel
    #
    @6
    cZ
    cn
    wcel
    #
    cZ
    cneg
    #
    cn
    wcel
    #
    w3o
    #
    wa
    @14
    @2
    wi
    #
    cZ
    elz
    @19
    @15
    @20
    @19
    @15
    @14
    @2
    @19
    @15
    @14
    wa
    #
    wa
    @2
    @8
    @19
    @21
    @8
    @6
    @21
    @8
    wi
    #
    @16
    @18
    @6
    @8
    @21
    @6
    @5
    @7
    3mix2
    a1d
    @21
    @16
    @8
    @14
    @16
    @8
    wi
    #
    @15
    @13
    @23
    @12
    @13
    @16
    @8
    @13
    @16
    wa
    @7
    @5
    @6
    @16
    @13
    @7
    cZ
    nnle1eq1
    biimpac
    3mix3d
    ex
    adantl
    adantl
    com12
    @18
    @17
    cz
    wcel
    #
    c1
    @17
    cle
    wbr
    #
    wa
    @22
    @17
    elnnz1
    @25
    @22
    @24
    @25
    @15
    @14
    @8
    @15
    @25
    @14
    @8
    wi
    #
    @15
    @25
    cZ
    @1
    cle
    wbr
    #
    @26
    c1
    cr
    wcel
    @15
    @25
    @27
    wb
    @15
    1red
    c1
    cZ
    lenegcon2
    mpancom
    @14
    @27
    @15
    @8
    @12
    @27
    @15
    @8
    wi
    #
    wi
    @13
    @12
    @27
    @28
    @15
    @12
    @27
    wa
    #
    @8
    @15
    @29
    @1
    cZ
    wceq
    @8
    @15
    @1
    cZ
    @1
    cr
    wcel
    @15
    neg1rr
    a1i
    @15
    id
    letri3d
    @8
    cZ
    @1
    @5
    @6
    @7
    3mix1
    eqcoms
    syl6bir
    com12
    ex
    adantr
    com13
    sylbid
    com12
    impd
    adantl
    sylbi
    3jaoi
    imp
    @21
    @2
    @8
    wb
    #
    @19
    @15
    @30
    @14
    cZ
    @1
    cc0
    c1
    cr
    eltpg
    adantr
    adantl
    mpbird
    exp32
    impcom
    sylbi
    sylbid
    impbid2
end
