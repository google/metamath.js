include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cdif.mm"
include "cn.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "cv.mm"
include "cmin.mm"
include "cvv.mm"
include "zex.mm"
include "difexg.mm"
include "mp1i.mm"
include "nnex.mm"
include "a1i.mm"
include "ovex.mm"
include "2a1i.mm"
include "cle.mm"
include "wa.mm"
include "wceq.mm"
include "simpl.mm"
include "peano2zd.mm"
include "simprl.mm"
include "zsubcld.mm"
include "cr.mm"
include "zre.mm"
include "ad2antrl.mm"
include "zred.mm"
include "1red.mm"
include "simprr.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "breqtrrd.mm"
include "lesubd.mm"
include "zcnd.mm"
include "nncand.mm"
include "eqcomd.mm"
include "jca31.mm"
include "adantrr.mm"
include "wb.mm"
include "eleq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "recnd.mm"
include "pncan2.mm"
include "eqbrtrd.mm"
include "subled.mm"
include "breq1.mm"
include "impbida.mm"
include "ellz1.mm"
include "anbi1d.mm"
include "elnnz1.mm"
include "3bitr4d.mm"
include "en2d.mm"
include "nnenom.mm"
include "entr.mm"

theorem lzenom
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( N e. ZZ -> ( ZZ \ ( ZZ>= ` ( N + 1 ) ) ) ~~ _om )

  proof
    cN
    cz
    wcel
    #
    cz
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cdif
    #
    cn
    cen
    wbr
    cn
    com
    cen
    wbr
    @3
    com
    cen
    wbr
    @0
    va
    vb
    @3
    cn
    @1
    va
    cv
    #
    cmin
    co
    #
    @1
    vb
    cv
    #
    cmin
    co
    #
    cz
    cvv
    wcel
    @3
    cvv
    wcel
    @0
    zex
    cz
    @2
    cvv
    difexg
    mp1i
    cn
    cvv
    wcel
    @0
    nnex
    a1i
    @5
    cvv
    wcel
    @0
    @4
    @3
    wcel
    #
    @1
    @4
    cmin
    ovex
    2a1i
    @7
    cvv
    wcel
    @0
    @6
    cn
    wcel
    #
    @1
    @6
    cmin
    ovex
    2a1i
    @0
    @4
    cz
    wcel
    #
    @4
    cN
    cle
    wbr
    #
    wa
    #
    @6
    @5
    wceq
    #
    wa
    #
    @6
    cz
    wcel
    #
    c1
    @6
    cle
    wbr
    #
    wa
    #
    @4
    @7
    wceq
    #
    wa
    #
    @8
    @13
    wa
    @9
    @18
    wa
    @0
    @14
    @19
    @0
    @14
    wa
    @19
    @5
    cz
    wcel
    #
    c1
    @5
    cle
    wbr
    #
    wa
    #
    @4
    @1
    @5
    cmin
    co
    #
    wceq
    #
    wa
    #
    @0
    @12
    @25
    @13
    @0
    @12
    wa
    #
    @20
    @21
    @24
    @26
    @1
    @4
    @26
    cN
    @0
    @12
    simpl
    peano2zd
    #
    @0
    @10
    @11
    simprl
    zsubcld
    @26
    @4
    @1
    c1
    @10
    @4
    cr
    wcel
    @0
    @11
    @4
    zre
    ad2antrl
    @26
    @1
    @27
    zred
    @26
    1red
    @26
    @4
    cN
    @1
    c1
    cmin
    co
    #
    cle
    @0
    @10
    @11
    simprr
    @26
    cN
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @28
    cN
    wceq
    @0
    @29
    @12
    cN
    zcn
    adantr
    ax-1cn
    cN
    c1
    pncan
    sylancl
    breqtrrd
    lesubd
    @26
    @23
    @4
    @26
    @1
    @4
    @26
    @1
    @27
    zcnd
    @10
    @4
    cc
    wcel
    @0
    @11
    @4
    zcn
    ad2antrl
    nncand
    eqcomd
    jca31
    adantrr
    @13
    @19
    @25
    wb
    @0
    @12
    @13
    @17
    @22
    @18
    @24
    @13
    @15
    @20
    @16
    @21
    @6
    @5
    cz
    eleq1
    @6
    @5
    c1
    cle
    breq2
    anbi12d
    @13
    @7
    @23
    @4
    @6
    @5
    @1
    cmin
    oveq2
    eqeq2d
    anbi12d
    ad2antll
    mpbird
    @0
    @19
    wa
    @14
    @7
    cz
    wcel
    #
    @7
    cN
    cle
    wbr
    #
    wa
    #
    @6
    @1
    @7
    cmin
    co
    #
    wceq
    #
    wa
    #
    @0
    @17
    @36
    @18
    @0
    @17
    wa
    #
    @31
    @32
    @35
    @37
    @1
    @6
    @37
    cN
    @0
    @17
    simpl
    peano2zd
    #
    @0
    @15
    @16
    simprl
    zsubcld
    @37
    @1
    cN
    @6
    @37
    @1
    @38
    zred
    @0
    cN
    cr
    wcel
    @17
    cN
    zre
    adantr
    #
    @15
    @6
    cr
    wcel
    @0
    @16
    @6
    zre
    ad2antrl
    @37
    @1
    cN
    cmin
    co
    #
    c1
    @6
    cle
    @37
    @29
    @30
    @40
    c1
    wceq
    @37
    cN
    @39
    recnd
    ax-1cn
    cN
    c1
    pncan2
    sylancl
    @0
    @15
    @16
    simprr
    eqbrtrd
    subled
    @37
    @34
    @6
    @37
    @1
    @6
    @37
    @1
    @38
    zcnd
    @15
    @6
    cc
    wcel
    @0
    @16
    @6
    zcn
    ad2antrl
    nncand
    eqcomd
    jca31
    adantrr
    @18
    @14
    @36
    wb
    @0
    @17
    @18
    @12
    @33
    @13
    @35
    @18
    @10
    @31
    @11
    @32
    @4
    @7
    cz
    eleq1
    @4
    @7
    cN
    cle
    breq1
    anbi12d
    @18
    @5
    @34
    @6
    @4
    @7
    @1
    cmin
    oveq2
    eqeq2d
    anbi12d
    ad2antll
    mpbird
    impbida
    @0
    @8
    @12
    @13
    @4
    cN
    ellz1
    anbi1d
    @0
    @9
    @17
    @18
    @9
    @17
    wb
    @0
    @6
    elnnz1
    a1i
    anbi1d
    3bitr4d
    en2d
    nnenom
    @3
    cn
    com
    entr
    sylancl
end
