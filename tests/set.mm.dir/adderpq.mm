include "cnpi.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cerq.mm"
include "cfv.mm"
include "cplq.mm"
include "co.mm"
include "cplpq.mm"
include "wceq.mm"
include "cnq.mm"
include "nqercl.mm"
include "addpqnq.mm"
include "syl2an.mm"
include "ceq.mm"
include "wbr.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "nqerrel.mm"
include "adantr.mm"
include "wb.mm"
include "wi.mm"
include "elpqn.mm"
include "syl.mm"
include "adderpqlem.mm"
include "3exp.mm"
include "mpd.mm"
include "imp.mm"
include "mpbid.mm"
include "adantl.mm"
include "mpan9.mm"
include "addcompq.mm"
include "3brtr3g.mm"
include "ertrd.mm"
include "addpqf.mm"
include "fovcl.mm"
include "nqereq.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "0nnq.mm"
include "cdm.mm"
include "nqerf.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "anim12i.mm"
include "con3i.mm"
include "addnqf.mm"
include "ndmov.mm"
include "0nelxp.mm"
include "mtbir.mm"
include "pm2.61i.mm"

theorem adderpq
  let cA: class A
  let cB: class B


  assert |- ( ( /Q ` A ) +Q ( /Q ` B ) ) = ( /Q ` ( A +pQ B ) )

  proof
    cA
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cerq
    cfv
    #
    cB
    cerq
    cfv
    #
    cplq
    co
    #
    cA
    cB
    cplpq
    co
    #
    cerq
    cfv
    #
    wceq
    @3
    @6
    @4
    @5
    cplpq
    co
    #
    cerq
    cfv
    #
    @8
    @1
    @4
    cnq
    wcel
    #
    @5
    cnq
    wcel
    #
    @6
    @10
    wceq
    @2
    cA
    nqercl
    #
    cB
    nqercl
    #
    @4
    @5
    addpqnq
    syl2an
    @3
    @7
    @9
    ceq
    wbr
    #
    @8
    @10
    wceq
    #
    @3
    @7
    @4
    cB
    cplpq
    co
    #
    @9
    ceq
    @0
    @0
    ceq
    wer
    @3
    enqer
    a1i
    @3
    cA
    @4
    ceq
    wbr
    #
    @7
    @17
    ceq
    wbr
    #
    @1
    @18
    @2
    cA
    nqerrel
    adantr
    @1
    @2
    @18
    @19
    wb
    #
    @1
    @4
    @0
    wcel
    #
    @2
    @20
    wi
    @1
    @11
    @21
    @13
    @4
    elpqn
    syl
    #
    @1
    @21
    @2
    @20
    cA
    @4
    cB
    adderpqlem
    3exp
    mpd
    imp
    mpbid
    @3
    cB
    @4
    cplpq
    co
    #
    @5
    @4
    cplpq
    co
    #
    @17
    @9
    ceq
    @3
    cB
    @5
    ceq
    wbr
    #
    @23
    @24
    ceq
    wbr
    #
    @2
    @25
    @1
    cB
    nqerrel
    adantl
    @1
    @21
    @2
    @25
    @26
    wb
    #
    @22
    @2
    @5
    @0
    wcel
    #
    @21
    @27
    wi
    @2
    @12
    @28
    @14
    @5
    elpqn
    syl
    #
    @2
    @28
    @21
    @27
    cB
    @5
    @4
    adderpqlem
    3exp
    mpd
    mpan9
    mpbid
    cB
    @4
    addcompq
    @5
    @4
    addcompq
    3brtr3g
    ertrd
    @3
    @7
    @0
    wcel
    @9
    @0
    wcel
    #
    @15
    @16
    wb
    cA
    cB
    @0
    @0
    @0
    cplpq
    addpqf
    fovcl
    @1
    @21
    @28
    @30
    @2
    @22
    @29
    @4
    @5
    @0
    @0
    @0
    cplpq
    addpqf
    fovcl
    syl2an
    @7
    @9
    nqereq
    syl2anc
    mpbid
    eqtr4d
    @3
    wn
    #
    @6
    c0
    @8
    @31
    @11
    @12
    wa
    #
    wn
    @6
    c0
    wceq
    @32
    @3
    @11
    @1
    @12
    @2
    @1
    @11
    @1
    wn
    #
    @11
    c0
    cnq
    wcel
    #
    0nnq
    @33
    @4
    c0
    cnq
    @1
    cA
    cerq
    cdm
    #
    wcel
    @4
    c0
    wceq
    @35
    @0
    cA
    @0
    cnq
    cerq
    nqerf
    fdmi
    #
    eleq2i
    cA
    cerq
    ndmfv
    sylnbir
    eleq1d
    mtbiri
    con4i
    @2
    @12
    @2
    wn
    #
    @12
    @34
    0nnq
    @37
    @5
    c0
    cnq
    @2
    cB
    @35
    wcel
    @5
    c0
    wceq
    @35
    @0
    cB
    @36
    eleq2i
    cB
    cerq
    ndmfv
    sylnbir
    eleq1d
    mtbiri
    con4i
    anim12i
    con3i
    @4
    @5
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    ndmov
    syl
    @31
    @7
    @35
    wcel
    #
    wn
    @8
    c0
    wceq
    @31
    @38
    c0
    @35
    wcel
    #
    @39
    c0
    @0
    wcel
    cnpi
    cnpi
    0nelxp
    @35
    @0
    c0
    @36
    eleq2i
    mtbir
    @31
    @7
    c0
    @35
    cA
    cB
    @0
    cplpq
    @0
    @0
    cxp
    @0
    cplpq
    addpqf
    fdmi
    ndmov
    eleq1d
    mtbiri
    @7
    cerq
    ndmfv
    syl
    eqtr4d
    pm2.61i
end
