include "c0.mm"
include "csn.mm"
include "c3o.mm"
include "cpw.mm"
include "wcel.mm"
include "c2o.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "c1o.mm"
include "ctp.mm"
include "wtru.mm"
include "cvv.mm"
include "tpex.mm"
include "a1i.mm"
include "snsstp1.mm"
include "sselpwd.mm"
include "trud.mm"
include "df3o2.mm"
include "pweqi.mm"
include "eleqtrri.mm"
include "0ex.mm"
include "snss.mm"
include "sylibr.mm"
include "snsstp3.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "prssd.mm"
include "simpl.mm"
include "wceq.mm"
include "wb.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "adantl.mm"
include "simpr.mm"
include "sseq2d.mm"
include "cleq2lem.mm"
include "1on.mm"
include "prid2.mm"
include "cif.mm"
include "iftrue.mm"
include "prex.mm"
include "fvmpt.mm"
include "adantr.mm"
include "syl5eleqr.mm"
include "wo.mm"
include "1n0.mm"
include "neii.mm"
include "csuc.mm"
include "eqcom.mm"
include "df-2o.mm"
include "df-1o.mm"
include "eqeq12i.mm"
include "suc11reg.mm"
include "3bitri.mm"
include "nemtbir.mm"
include "pm3.2ni.mm"
include "elpri.mm"
include "mto.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "wne.mm"
include "2on0.mm"
include "nelsn.mm"
include "ax-mp.mm"
include "nelneq2.mm"
include "mp2an.mm"
include "iffalsei.mm"
include "syl6eq.mm"
include "neleqtrrd.mm"
include "nelss.mm"
include "syl2anc.mm"
include "snsspr1.mm"
include "jctil.mm"
include "rspcedvd.mm"

theorem clsk1indlem1
  let vt: setvar t
  let cK: class K
  let vs: setvar s
  let vr: setvar r
  assume clsk1indlem.k: |- K = ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) )

  disjoint K s
  disjoint K t
  disjoint s t
  disjoint r s
  disjoint r t
  assert |- E. s e. ~P 3o E. t e. ~P 3o ( s C_ t /\ -. ( K ` s ) C_ ( K ` t ) )

  proof
    c0
    csn
    #
    c3o
    cpw
    #
    wcel
    #
    c0
    c2o
    cpr
    #
    @1
    wcel
    #
    vs
    cv
    #
    vt
    cv
    #
    wss
    #
    @5
    cK
    cfv
    #
    @6
    cK
    cfv
    #
    wss
    #
    wn
    #
    wa
    #
    vt
    @1
    wrex
    #
    vs
    @1
    wrex
    @0
    c0
    c1o
    c2o
    ctp
    #
    cpw
    #
    @1
    @0
    @15
    wcel
    wtru
    @0
    @14
    cvv
    @14
    cvv
    wcel
    wtru
    c0
    c1o
    c2o
    tpex
    a1i
    #
    @0
    @14
    wss
    #
    wtru
    c0
    c1o
    c2o
    snsstp1
    a1i
    #
    sselpwd
    trud
    c3o
    @14
    df3o2
    pweqi
    #
    eleqtrri
    @3
    @15
    @1
    @3
    @15
    wcel
    wtru
    @3
    @14
    cvv
    @16
    wtru
    c0
    c2o
    @14
    wtru
    @17
    c0
    @14
    wcel
    @18
    c0
    @14
    0ex
    snss
    sylibr
    wtru
    c2o
    csn
    @14
    wss
    #
    c2o
    @14
    wcel
    @20
    wtru
    c0
    c1o
    c2o
    snsstp3
    a1i
    c2o
    @14
    c2o
    con0
    2on
    elexi
    #
    snss
    sylibr
    prssd
    sselpwd
    trud
    @19
    eleqtrri
    @2
    @4
    wa
    #
    @13
    @0
    @6
    wss
    #
    @0
    cK
    cfv
    #
    @9
    wss
    #
    wn
    #
    wa
    #
    vt
    @1
    wrex
    #
    vs
    @0
    @1
    @2
    @4
    simpl
    @5
    @0
    wceq
    #
    @13
    @28
    wb
    @22
    @29
    @12
    @27
    vt
    @1
    @29
    @7
    @23
    @11
    @26
    @5
    @0
    @6
    sseq1
    @29
    @10
    @25
    @29
    @8
    @24
    @9
    @5
    @0
    cK
    fveq2
    sseq1d
    notbid
    anbi12d
    rexbidv
    adantl
    @22
    @27
    @0
    @3
    wss
    #
    @24
    @3
    cK
    cfv
    #
    wss
    #
    wn
    #
    wa
    #
    vt
    @3
    @1
    @2
    @4
    simpr
    @6
    @3
    wceq
    #
    @27
    @34
    wb
    @22
    @26
    @33
    @6
    @3
    @0
    @35
    @25
    @32
    @35
    @9
    @31
    @24
    @6
    @3
    cK
    fveq2
    sseq2d
    notbid
    cleq2lem
    adantl
    @22
    @33
    @30
    @22
    c1o
    @24
    wcel
    c1o
    @31
    wcel
    wn
    @33
    @22
    c1o
    c0
    c1o
    cpr
    #
    @24
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    @2
    @24
    @36
    wceq
    @4
    vr
    @0
    vr
    cv
    #
    @0
    wceq
    #
    @36
    @37
    cif
    #
    @36
    @1
    cK
    @38
    @36
    @37
    iftrue
    clsk1indlem.k
    c0
    c1o
    prex
    fvmpt
    adantr
    syl5eleqr
    @22
    @31
    @3
    c1o
    c1o
    @3
    wcel
    #
    wn
    @22
    @40
    c1o
    c0
    wceq
    #
    c1o
    c2o
    wceq
    #
    wo
    @41
    @42
    c1o
    c0
    1n0
    neii
    @42
    c1o
    c0
    1n0
    @42
    c2o
    c1o
    wceq
    c1o
    csuc
    #
    c0
    csuc
    #
    wceq
    @41
    c1o
    c2o
    eqcom
    c2o
    @43
    c1o
    @44
    df-2o
    df-1o
    eqeq12i
    c1o
    c0
    suc11reg
    3bitri
    nemtbir
    pm3.2ni
    c1o
    c0
    c2o
    elpri
    mto
    a1i
    @4
    @31
    @3
    wceq
    @2
    vr
    @3
    @39
    @3
    @1
    cK
    @37
    @3
    wceq
    #
    @39
    @3
    @0
    wceq
    #
    @36
    @3
    cif
    @3
    @45
    @38
    @46
    @37
    @3
    @36
    @37
    @3
    @0
    eqeq1
    @45
    id
    ifbieq2d
    @46
    @36
    @3
    c2o
    @3
    wcel
    c2o
    @0
    wcel
    wn
    #
    @46
    wn
    c0
    c2o
    @21
    prid2
    c2o
    c0
    wne
    @47
    2on0
    c2o
    c0
    nelsn
    ax-mp
    c2o
    @3
    @0
    nelneq2
    mp2an
    iffalsei
    syl6eq
    clsk1indlem.k
    c0
    c2o
    prex
    fvmpt
    adantl
    neleqtrrd
    c1o
    @24
    @31
    nelss
    syl2anc
    c0
    c2o
    snsspr1
    jctil
    rspcedvd
    rspcedvd
    mp2an
end
