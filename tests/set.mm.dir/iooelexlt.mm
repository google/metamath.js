include "cxr.mm"
include "wcel.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "eliooxr.mm"
include "simpld.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "wi.mm"
include "elxr.mm"
include "wa.mm"
include "wal.mm"
include "19.3v.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "cvv.mm"
include "ovex.mm"
include "nfcv.mm"
include "nfre1.mm"
include "elioore.mm"
include "readdcl.mm"
include "rehalfcld.mm"
include "sylan2.mm"
include "ancoms.mm"
include "rexrd.mm"
include "eliooord.mm"
include "adantr.mm"
include "wb.mm"
include "avglt1.mm"
include "mpbid.mm"
include "simprd.mm"
include "avglt2.mm"
include "xrlttrd.mm"
include "w3a.mm"
include "elioo1.mm"
include "syl.mm"
include "mpbir3and.mm"
include "jca.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibr.mm"
include "rspe.mm"
include "syl6.mm"
include "spcimgf.mm"
include "ax-mp.mm"
include "sylbir.mm"
include "expcom.mm"
include "simpl.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "adantl.mm"
include "wn.mm"
include "pnfxr.mm"
include "elioo2.mm"
include "mpan.mm"
include "biimpd.mm"
include "rexr.mm"
include "pnfnlt.mm"
include "intn3an2d.mm"
include "a1i.mm"
include "pm2.65d.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "mpd.mm"
include "c1.mm"
include "cmin.mm"
include "peano2rem.mm"
include "mnflt.mm"
include "ltm1d.mm"
include "mnfxr.mm"
include "mpbird.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "mpcom.mm"

theorem iooelexlt
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X

  disjoint A y
  disjoint B y
  disjoint X y
  assert |- ( X e. ( A (,) B ) -> E. y e. ( A (,) B ) y < X )

  proof
    cA
    cxr
    wcel
    #
    cX
    cA
    cB
    cioo
    co
    #
    wcel
    #
    vy
    cv
    #
    cX
    clt
    wbr
    #
    vy
    @1
    wrex
    #
    @2
    @0
    cB
    cxr
    wcel
    #
    cX
    cA
    cB
    eliooxr
    #
    simpld
    @0
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    @2
    @5
    wi
    #
    cA
    elxr
    @8
    @11
    @9
    @10
    @2
    @8
    @5
    @2
    @8
    wa
    #
    @12
    vy
    wal
    #
    @5
    @12
    vy
    19.3v
    cA
    cX
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cvv
    wcel
    @13
    @5
    wi
    @14
    c2
    cdiv
    ovex
    @12
    @5
    vy
    @15
    cvv
    vy
    @15
    nfcv
    @4
    vy
    @1
    nfre1
    #
    @3
    @15
    wceq
    #
    @12
    @3
    @1
    wcel
    #
    @4
    wa
    #
    @5
    @12
    @19
    @17
    @15
    @1
    wcel
    #
    @15
    cX
    clt
    wbr
    #
    wa
    @12
    @20
    @21
    @12
    @20
    @15
    cxr
    wcel
    #
    cA
    @15
    clt
    wbr
    #
    @15
    cB
    clt
    wbr
    #
    @12
    @15
    @8
    @2
    @15
    cr
    wcel
    #
    @2
    @8
    cX
    cr
    wcel
    #
    @25
    cX
    cA
    cB
    elioore
    #
    @8
    @26
    wa
    @14
    cA
    cX
    readdcl
    rehalfcld
    sylan2
    ancoms
    rexrd
    #
    @12
    cA
    cX
    clt
    wbr
    #
    @23
    @2
    @29
    @8
    @2
    @29
    cX
    cB
    clt
    wbr
    #
    cX
    cA
    cB
    eliooord
    #
    simpld
    adantr
    #
    @8
    @2
    @29
    @23
    wb
    #
    @2
    @8
    @26
    @33
    @27
    cA
    cX
    avglt1
    sylan2
    ancoms
    mpbid
    @12
    @15
    cX
    cB
    @28
    @2
    cX
    cxr
    wcel
    #
    @8
    @2
    cX
    @27
    rexrd
    #
    adantr
    @2
    @6
    @8
    @2
    @0
    @6
    @7
    simprd
    #
    adantr
    @12
    @29
    @21
    @32
    @8
    @2
    @29
    @21
    wb
    #
    @2
    @8
    @26
    @37
    @27
    cA
    cX
    avglt2
    sylan2
    ancoms
    mpbid
    #
    @2
    @30
    @8
    @2
    @29
    @30
    @31
    simprd
    #
    adantr
    xrlttrd
    @2
    @20
    @22
    @23
    @24
    w3a
    wb
    #
    @8
    @2
    @0
    @6
    wa
    @40
    @7
    cA
    cB
    @15
    elioo1
    syl
    adantr
    mpbir3and
    @38
    jca
    @17
    @18
    @20
    @4
    @21
    @3
    @15
    @1
    eleq1
    @3
    @15
    cX
    clt
    breq1
    anbi12d
    syl5ibr
    @4
    vy
    @1
    rspe
    #
    syl6
    spcimgf
    ax-mp
    sylbir
    expcom
    @2
    @9
    @5
    @2
    @9
    wa
    #
    @2
    @5
    @2
    @9
    simpl
    @42
    @2
    cX
    cpnf
    cB
    cioo
    co
    #
    wcel
    #
    @5
    @9
    @2
    @44
    wb
    @2
    @9
    @1
    @43
    cX
    cA
    cpnf
    cB
    cioo
    oveq1
    eleq2d
    adantl
    @2
    @44
    @5
    wi
    @9
    @2
    @44
    @5
    @2
    @6
    @44
    wn
    @36
    @6
    @44
    @26
    cpnf
    cX
    clt
    wbr
    #
    @30
    w3a
    #
    @6
    @44
    @46
    cpnf
    cxr
    wcel
    @6
    @44
    @46
    wb
    pnfxr
    cpnf
    cB
    cX
    elioo2
    mpan
    biimpd
    @44
    @46
    wn
    #
    wi
    @6
    @44
    @26
    @47
    cX
    cpnf
    cB
    elioore
    @26
    @45
    @26
    @30
    @26
    @34
    @45
    wn
    cX
    rexr
    cX
    pnfnlt
    syl
    intn3an2d
    syl
    a1i
    pm2.65d
    syl
    pm2.21d
    adantr
    sylbid
    mpd
    expcom
    @2
    @10
    @5
    @2
    @10
    wa
    #
    @48
    vy
    wal
    #
    @5
    @48
    vy
    19.3v
    cX
    c1
    cmin
    co
    #
    cvv
    wcel
    @49
    @5
    wi
    cX
    c1
    cmin
    ovex
    @48
    @5
    vy
    @50
    cvv
    vy
    @50
    nfcv
    @16
    @48
    @3
    @50
    wceq
    #
    @5
    @48
    @51
    wa
    #
    @19
    @5
    @52
    @19
    @50
    @1
    wcel
    #
    @50
    cX
    clt
    wbr
    #
    wa
    #
    @48
    @55
    @51
    @48
    @53
    @54
    @48
    @53
    @50
    cmnf
    cB
    cioo
    co
    #
    wcel
    #
    @2
    @57
    @10
    @2
    @57
    @50
    cr
    wcel
    #
    cmnf
    @50
    clt
    wbr
    #
    @50
    cB
    clt
    wbr
    #
    @2
    @26
    @58
    @27
    cX
    peano2rem
    syl
    #
    @2
    @58
    @59
    @61
    @50
    mnflt
    syl
    @2
    @50
    cX
    cB
    @2
    @50
    @61
    rexrd
    @35
    @36
    @2
    cX
    @27
    ltm1d
    #
    @39
    xrlttrd
    @2
    @6
    @57
    @58
    @59
    @60
    w3a
    wb
    #
    @36
    cmnf
    cxr
    wcel
    @6
    @63
    mnfxr
    cmnf
    cB
    @50
    elioo2
    mpan
    syl
    mpbir3and
    adantr
    @10
    @53
    @57
    wb
    @2
    @10
    @1
    @56
    @50
    cA
    cmnf
    cB
    cioo
    oveq1
    eleq2d
    adantl
    mpbird
    @2
    @54
    @10
    @62
    adantr
    jca
    adantr
    @51
    @19
    @55
    wb
    @48
    @51
    @18
    @53
    @4
    @54
    @3
    @50
    @1
    eleq1
    @3
    @50
    cX
    clt
    breq1
    anbi12d
    adantl
    mpbird
    @41
    syl
    expcom
    spcimgf
    ax-mp
    sylbir
    expcom
    3jaoi
    sylbi
    mpcom
end
