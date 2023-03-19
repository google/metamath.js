include "cnpi.mm"
include "wcel.mm"
include "c1o.mm"
include "wceq.mm"
include "clti.mm"
include "wbr.mm"
include "wi.mm"
include "cv.mm"
include "1pi.mm"
include "elexi.mm"
include "eqvinc.mm"
include "mpbiri.mm"
include "gencl.mm"
include "eqcoms.mm"
include "a1i.mm"
include "com.mm"
include "wss.mm"
include "wa.mm"
include "pinn.mm"
include "c0.mm"
include "elni2.mm"
include "csuc.mm"
include "word.mm"
include "nnord.mm"
include "ordsucss.mm"
include "syl.mm"
include "df-1o.mm"
include "sseq1i.mm"
include "syl6ibr.mm"
include "imp.mm"
include "sylbi.mm"
include "1onn.mm"
include "eleq1.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "wne.mm"
include "peano2b.mm"
include "syl6bbr.mm"
include "syl5ib.mm"
include "adantrd.mm"
include "wb.mm"
include "ltpiord.mm"
include "mpan.mm"
include "biimpa.mm"
include "eleq2.mm"
include "wo.mm"
include "elsuci.mm"
include "ne0i.mm"
include "0lt1o.mm"
include "mpbii.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "syl5.mm"
include "jcad.mm"
include "elni.mm"
include "simpr.mm"
include "cpli.mm"
include "co.mm"
include "addclpi.mm"
include "mpan2.mm"
include "coa.mm"
include "addpiord.mm"
include "con0.mm"
include "pion.mm"
include "oa1suc.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "biimparc.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "ex.mm"
include "pm2.43d.mm"
include "biimprd.mm"
include "anim12d.mm"
include "impbid.mm"
include "imbi1d.mm"
include "syl6bir.mm"
include "adantr.mm"
include "com12.mm"
include "pm5.74d.mm"
include "bitrd.mm"
include "2a1i.mm"
include "pm5.32i.mm"
include "simplbi2.mm"
include "imim1d.mm"
include "ltrelpi.mm"
include "brel.mm"
include "ibi.mm"
include "jao.mm"
include "mpi.mm"
include "syl6com.mm"
include "impd.mm"
include "cvv.mm"
include "0ex.mm"
include "sucssel.mm"
include "ax-mp.mm"
include "sylbir.mm"
include "sylan2.mm"
include "syl9r.mm"
include "adantlr.mm"
include "findsg.mm"
include "mpanl2.mm"
include "syl2anc.mm"
include "expd.mm"
include "pm2.43i.mm"
include "wn.mm"
include "nlt1pi.mm"
include "wor.mm"
include "ltsopi.mm"
include "sotric.mm"
include "mtbii.mm"
include "notnotrd.mm"
include "mpjaod.mm"

theorem indpi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume indpi.1: |- ( x = 1o -> ( ph <-> ps ) )
  assume indpi.2: |- ( x = y -> ( ph <-> ch ) )
  assume indpi.3: |- ( x = ( y +N 1o ) -> ( ph <-> th ) )
  assume indpi.4: |- ( x = A -> ( ph <-> ta ) )
  assume indpi.5: |- ps
  assume indpi.6: |- ( y e. N. -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. N. -> ta )

  proof
    cA
    cnpi
    wcel
    #
    cA
    c1o
    wceq
    #
    wta
    c1o
    cA
    clti
    wbr
    #
    @1
    wta
    wi
    @0
    wta
    c1o
    cA
    wph
    wta
    vx
    cv
    #
    c1o
    wceq
    #
    c1o
    cA
    wceq
    vx
    @3
    cA
    vx
    c1o
    cA
    c1o
    cnpi
    1pi
    elexi
    #
    eqvinc
    indpi.4
    @4
    wph
    wps
    indpi.5
    indpi.1
    mpbiri
    #
    gencl
    eqcoms
    a1i
    @0
    @2
    wta
    wi
    @0
    @0
    @2
    wta
    @0
    cA
    com
    wcel
    #
    c1o
    cA
    wss
    #
    @0
    @2
    wa
    #
    wta
    wi
    #
    cA
    pinn
    @0
    @7
    c0
    cA
    wcel
    #
    wa
    @8
    cA
    elni2
    @7
    @11
    @8
    @7
    @11
    c0
    csuc
    #
    cA
    wss
    #
    @8
    @7
    cA
    word
    @11
    @13
    wi
    cA
    nnord
    c0
    cA
    ordsucss
    syl
    c1o
    @12
    cA
    df-1o
    sseq1i
    syl6ibr
    imp
    sylbi
    @7
    c1o
    com
    wcel
    #
    @8
    @10
    1onn
    @3
    cnpi
    wcel
    #
    c1o
    @3
    clti
    wbr
    #
    wa
    #
    wph
    wi
    #
    c1o
    cnpi
    wcel
    #
    c1o
    c1o
    clti
    wbr
    #
    wa
    #
    wps
    wi
    vy
    cv
    #
    cnpi
    wcel
    #
    c1o
    @22
    clti
    wbr
    #
    wa
    #
    wch
    wi
    #
    @23
    c1o
    @22
    csuc
    #
    clti
    wbr
    #
    wa
    #
    wth
    wi
    #
    @10
    vx
    vy
    cA
    c1o
    @4
    @17
    @21
    wph
    wps
    @4
    @15
    @19
    @16
    @20
    @3
    c1o
    cnpi
    eleq1
    @3
    c1o
    c1o
    clti
    breq2
    anbi12d
    indpi.1
    imbi12d
    @3
    @22
    wceq
    #
    @17
    @25
    wph
    wch
    @31
    @15
    @23
    @16
    @24
    @3
    @22
    cnpi
    eleq1
    @3
    @22
    c1o
    clti
    breq2
    anbi12d
    indpi.2
    imbi12d
    @3
    @27
    wceq
    #
    @18
    @29
    wph
    wi
    @30
    @32
    @17
    @29
    wph
    @32
    @17
    @29
    @32
    @17
    @23
    @28
    @32
    @17
    @22
    com
    wcel
    #
    @22
    c0
    wne
    #
    wa
    @23
    @32
    @17
    @33
    @34
    @32
    @15
    @33
    @16
    @15
    @3
    com
    wcel
    #
    @32
    @33
    @3
    pinn
    @32
    @35
    @27
    com
    wcel
    @33
    @3
    @27
    com
    eleq1
    @22
    peano2b
    syl6bbr
    syl5ib
    adantrd
    @17
    c1o
    @3
    wcel
    #
    @32
    @34
    @15
    @16
    @36
    @19
    @15
    @16
    @36
    wb
    1pi
    c1o
    @3
    ltpiord
    mpan
    biimpa
    @32
    @36
    c1o
    @27
    wcel
    #
    @34
    @3
    @27
    c1o
    eleq2
    @37
    c1o
    @22
    wcel
    #
    c1o
    @22
    wceq
    #
    wo
    #
    @34
    c1o
    @22
    elsuci
    #
    @38
    @34
    @39
    @22
    c1o
    ne0i
    @39
    c0
    @22
    wcel
    #
    @34
    @39
    c0
    c1o
    wcel
    @42
    0lt1o
    c1o
    @22
    c0
    eleq2
    mpbii
    @22
    c0
    ne0i
    syl
    jaoi
    syl
    syl6bi
    syl5
    jcad
    @22
    elni
    syl6ibr
    @17
    @16
    @32
    @28
    @15
    @16
    simpr
    @3
    @27
    c1o
    clti
    breq2
    #
    syl5ib
    jcad
    @32
    @23
    @15
    @28
    @16
    @32
    @23
    @15
    @32
    @23
    @23
    @15
    wi
    @23
    @15
    @32
    @23
    wa
    #
    @22
    c1o
    cpli
    co
    #
    cnpi
    wcel
    #
    @23
    @19
    @46
    1pi
    @22
    c1o
    addclpi
    mpan2
    @44
    @3
    @45
    cnpi
    @23
    @3
    @45
    wceq
    #
    @32
    @23
    @45
    @27
    @3
    @23
    @45
    @22
    c1o
    coa
    co
    #
    @27
    @23
    @19
    @45
    @48
    wceq
    1pi
    @22
    c1o
    addpiord
    mpan2
    @23
    @22
    con0
    wcel
    @48
    @27
    wceq
    @22
    pion
    @22
    oa1suc
    syl
    eqtrd
    eqeq2d
    #
    biimparc
    eleq1d
    syl5ibr
    ex
    pm2.43d
    @32
    @16
    @28
    @43
    biimprd
    anim12d
    impbid
    imbi1d
    @32
    @29
    wph
    wth
    @29
    @32
    wph
    wth
    wb
    #
    @23
    @32
    @50
    wi
    @28
    @23
    @32
    @47
    @50
    @49
    indpi.3
    syl6bir
    adantr
    com12
    pm5.74d
    bitrd
    @3
    cA
    wceq
    #
    @17
    @9
    wph
    wta
    @51
    @15
    @0
    @16
    @2
    @3
    cA
    cnpi
    eleq1
    @3
    cA
    c1o
    clti
    breq2
    anbi12d
    indpi.4
    imbi12d
    wps
    @14
    @21
    indpi.5
    2a1i
    @33
    c1o
    @22
    wss
    #
    @26
    @30
    wi
    @14
    @26
    @29
    wch
    @33
    @52
    wa
    wth
    @26
    @23
    @28
    wch
    @23
    @26
    @38
    wch
    wi
    #
    @28
    wch
    wi
    @23
    @38
    @25
    wch
    @25
    @23
    @38
    @23
    @24
    @38
    @19
    @23
    @24
    @38
    wb
    1pi
    c1o
    @22
    ltpiord
    mpan
    pm5.32i
    simplbi2
    imim1d
    @28
    @37
    @53
    wch
    @28
    @37
    @28
    @19
    @27
    cnpi
    wcel
    wa
    @28
    @37
    wb
    c1o
    @27
    cnpi
    cnpi
    clti
    ltrelpi
    brel
    c1o
    @27
    ltpiord
    syl
    ibi
    @37
    @40
    @53
    wch
    @41
    @53
    @39
    wch
    wi
    @40
    wch
    wi
    wph
    wch
    @4
    @39
    vx
    @3
    @22
    vx
    c1o
    @22
    @5
    eqvinc
    indpi.2
    @6
    gencl
    @38
    wch
    @39
    jao
    mpi
    syl5
    syl5
    syl6com
    impd
    @52
    @33
    @42
    wch
    wth
    wi
    #
    @52
    @12
    @22
    wss
    #
    @42
    c1o
    @12
    @22
    df-1o
    sseq1i
    c0
    cvv
    wcel
    @55
    @42
    wi
    0ex
    c0
    @22
    cvv
    sucssel
    ax-mp
    sylbi
    @33
    @42
    wa
    @23
    @54
    @22
    elni2
    indpi.6
    sylbir
    sylan2
    syl9r
    adantlr
    findsg
    mpanl2
    syl2anc
    expd
    pm2.43i
    @0
    @1
    @2
    wo
    #
    @0
    cA
    c1o
    clti
    wbr
    #
    @56
    wn
    #
    cA
    nlt1pi
    @0
    @19
    @57
    @58
    wb
    #
    1pi
    cnpi
    clti
    wor
    @0
    @19
    wa
    @59
    ltsopi
    cnpi
    cA
    c1o
    clti
    sotric
    mpan
    mpan2
    mtbii
    notnotrd
    mpjaod
end
