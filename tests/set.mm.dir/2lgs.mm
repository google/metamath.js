include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "cprime.mm"
include "wcel.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "wb.mm"
include "prm2orodd.mm"
include "wi.mm"
include "2lgslem4.mm"
include "a1i.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "3bitr4d.mm"
include "a1d.mm"
include "wa.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "c4.mm"
include "cfl.mm"
include "cfv.mm"
include "cexp.mm"
include "cz.mm"
include "cv.mm"
include "cmul.mm"
include "clt.mm"
include "cfz.mm"
include "wrex.mm"
include "crab.mm"
include "chash.mm"
include "cn.mm"
include "2prm.mm"
include "prmnn.mm"
include "dvdsprime.mm"
include "sylancr.mm"
include "z2even.mm"
include "breq2.mm"
include "mpbiri.mm"
include "eleq1.mm"
include "1nprm.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "con3dimp.mm"
include "2z.mm"
include "jctil.mm"
include "2lgslem1.mm"
include "eqcomd.mm"
include "w3a.mm"
include "cif.mm"
include "cmpt.mm"
include "csn.mm"
include "cdif.mm"
include "nnoddn2prmb.mm"
include "biimpri.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "gausslemma2d.mm"
include "mpd3an23.mm"
include "2lgslem2.mm"
include "m1exp1.mm"
include "syl.mm"
include "cc0.mm"
include "2nn.mm"
include "dvdsval3.mm"
include "2lgslem3.mm"
include "sylan.mm"
include "ax-1.mm"
include "iffalse.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "eqneqall.mm"
include "mpi.mm"
include "pm2.61i.mm"
include "iftrue.mm"
include "impbii.mm"
include "3bitrd.mm"
include "expcom.mm"
include "mpcom.mm"

theorem 2lgs
  let cP: class P
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y


  assert |- ( P e. Prime -> ( ( 2 /L P ) = 1 <-> ( P mod 8 ) e. { 1 , 7 } ) )

  proof
    cP
    c2
    wceq
    #
    c2
    cP
    cdvds
    wbr
    #
    wn
    #
    wo
    cP
    cprime
    wcel
    #
    c2
    cP
    clgs
    co
    #
    c1
    wceq
    #
    cP
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    wcel
    #
    wb
    #
    cP
    prm2orodd
    @0
    @3
    @9
    wi
    @2
    @0
    @9
    @3
    @0
    c2
    c2
    clgs
    co
    #
    c1
    wceq
    #
    c2
    c8
    cmo
    co
    #
    @7
    wcel
    #
    @5
    @8
    @11
    @13
    wb
    @0
    2lgslem4
    a1i
    @0
    @4
    @10
    c1
    cP
    c2
    c2
    clgs
    oveq2
    eqeq1d
    @0
    @6
    @12
    @7
    cP
    c2
    c8
    cmo
    oveq1
    eleq1d
    3bitr4d
    a1d
    @3
    @2
    @9
    @3
    @2
    wa
    #
    @5
    c1
    cneg
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cP
    c4
    cdiv
    co
    cfl
    cfv
    #
    cmin
    co
    #
    cexp
    co
    #
    c1
    wceq
    #
    c2
    @17
    cdvds
    wbr
    #
    @8
    @14
    c2
    cz
    wcel
    #
    cP
    c2
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    @17
    vx
    cv
    #
    vi
    cv
    c2
    cmul
    co
    wceq
    cP
    c2
    cdiv
    co
    #
    @25
    cP
    cmo
    co
    clt
    wbr
    wa
    vi
    c1
    @15
    cfz
    co
    #
    wrex
    vx
    cz
    crab
    chash
    cfv
    #
    wceq
    #
    @5
    @19
    wb
    @14
    @23
    @21
    @3
    @22
    @1
    @3
    @22
    @0
    cP
    c1
    wceq
    #
    wo
    #
    @1
    @3
    c2
    cprime
    wcel
    cP
    cn
    wcel
    #
    @22
    @31
    wb
    2prm
    cP
    prmnn
    #
    c2
    cP
    dvdsprime
    sylancr
    @31
    @3
    @1
    @0
    @3
    @1
    wi
    @30
    @0
    @1
    @3
    @0
    @1
    c2
    c2
    cdvds
    wbr
    z2even
    cP
    c2
    c2
    cdvds
    breq2
    mpbiri
    a1d
    @30
    @3
    c1
    cprime
    wcel
    #
    @1
    cP
    c1
    cprime
    eleq1
    @34
    @1
    1nprm
    pm2.21i
    syl6bi
    jaoi
    com12
    sylbid
    con3dimp
    2z
    jctil
    @14
    @28
    @17
    vx
    cP
    vi
    2lgslem1
    eqcomd
    @14
    @24
    @29
    w3a
    #
    @4
    @18
    c1
    @35
    vy
    cP
    vy
    @27
    vy
    cv
    c2
    cmul
    co
    #
    @26
    clt
    wbr
    @36
    cP
    @36
    cmin
    co
    cif
    cmpt
    #
    @15
    @16
    @17
    @14
    @24
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @29
    @38
    @14
    cP
    nnoddn2prmb
    biimpri
    3ad2ant1
    @15
    eqid
    @37
    eqid
    @16
    eqid
    @17
    eqid
    #
    gausslemma2d
    eqeq1d
    mpd3an23
    @14
    @17
    cz
    wcel
    #
    @19
    @20
    wb
    cP
    @17
    @39
    2lgslem2
    #
    @17
    m1exp1
    syl
    @14
    @20
    @17
    c2
    cmo
    co
    #
    cc0
    wceq
    #
    @8
    cc0
    c1
    cif
    #
    cc0
    wceq
    #
    @8
    @14
    c2
    cn
    wcel
    @40
    @20
    @43
    wb
    2nn
    @41
    c2
    @17
    dvdsval3
    sylancr
    @14
    @42
    @44
    cc0
    @3
    @32
    @2
    @42
    @44
    wceq
    @33
    cP
    @17
    @39
    2lgslem3
    sylan
    eqeq1d
    @45
    @8
    wb
    @14
    @45
    @8
    @8
    @45
    @8
    wi
    @8
    @45
    ax-1
    @8
    wn
    #
    @45
    c1
    cc0
    wceq
    #
    @8
    @46
    @44
    c1
    cc0
    @8
    cc0
    c1
    iffalse
    eqeq1d
    @47
    c1
    cc0
    wne
    @8
    ax-1ne0
    @8
    c1
    cc0
    eqneqall
    mpi
    syl6bi
    pm2.61i
    @8
    cc0
    c1
    iftrue
    impbii
    a1i
    3bitrd
    3bitrd
    expcom
    jaoi
    mpcom
end
