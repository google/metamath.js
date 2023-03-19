include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "wfn.mm"
include "bnj1232.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "simpr3.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "bnj923.mm"
include "wb.mm"
include "peano2.mm"
include "eleq1.mm"
include "bianir.mm"
include "syl2an.mm"
include "sylan.mm"
include "csn.mm"
include "cun.mm"
include "df-suc.mm"
include "eqeq2i.mm"
include "wss.mm"
include "ssun2.mm"
include "vex.mm"
include "snnz.mm"
include "ssn0.mm"
include "mp2an.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "cdif.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "syl2anc.mm"

theorem bnj970
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vp: setvar p
  assume bnj970.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj970.10: |- D = ( _om \ { (/) } )


  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> p e. D )

  proof
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    wa
    #
    wch
    vn
    cv
    #
    vm
    cv
    csuc
    wceq
    #
    vp
    cv
    #
    @1
    csuc
    #
    wceq
    #
    w3a
    #
    wa
    @1
    cD
    wcel
    #
    @5
    @3
    cD
    wcel
    #
    @6
    @7
    @0
    wch
    @2
    @7
    @5
    wch
    @7
    vf
    cv
    @1
    wfn
    wph
    wps
    bnj970.3
    bnj1232
    3ad2ant1
    adantl
    @0
    wch
    @2
    @5
    simpr3
    @7
    @5
    wa
    @3
    com
    wcel
    #
    @3
    c0
    wne
    #
    @8
    @7
    @1
    com
    wcel
    #
    @5
    @9
    cD
    vn
    bnj970.10
    bnj923
    @11
    @4
    com
    wcel
    #
    @9
    @12
    wb
    @9
    @5
    @1
    peano2
    @3
    @4
    com
    eleq1
    @12
    @9
    bianir
    syl2an
    sylan
    @5
    @10
    @7
    @5
    @3
    @1
    @1
    csn
    #
    cun
    #
    wceq
    #
    @10
    @4
    @14
    @3
    @1
    df-suc
    eqeq2i
    @15
    @10
    @14
    c0
    wne
    #
    @13
    @14
    wss
    @13
    c0
    wne
    @16
    @13
    @1
    ssun2
    @1
    vn
    vex
    snnz
    @13
    @14
    ssn0
    mp2an
    @3
    @14
    c0
    neeq1
    mpbiri
    sylbi
    adantl
    @8
    @3
    com
    c0
    csn
    cdif
    #
    wcel
    @9
    @10
    wa
    cD
    @17
    @3
    bnj970.10
    eleq2i
    @3
    com
    c0
    eldifsn
    bitri
    sylanbrc
    syl2anc
end
