include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cfv.mm"
include "cmpt.mm"
include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cc0.mm"
include "cfz.mm"
include "wf1.mm"
include "wss.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "eqid.mm"
include "mapsnf1o2.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "csn.mm"
include "cxp.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "f1ores.mm"
include "sylancr.mm"
include "ccnv.mm"
include "coe1mul2lem1.mm"
include "rabbidva.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "syl6eqr.mm"
include "mptpreima.mm"
include "3eqtr4g.mm"
include "imaeq2d.mm"
include "wfo.mm"
include "f1ofo.mm"
include "fz0ssnn0.mm"
include "foimacnv.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "f1oeq3d.mm"
include "wb.mm"
include "resmpt.mm"
include "f1oeq1.mm"
include "3syl.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem coe1mul2lem2
  let vk: setvar k
  let cH: class H
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let va: setvar a
  let cX: class X
  assume coe1mul2lem2.h: |- H = { d e. ( NN0 ^m 1o ) | d oR <_ ( 1o X. { k } ) }

  disjoint H c
  disjoint c d
  disjoint c k
  disjoint d k
  disjoint A a
  disjoint X a
  assert |- ( k e. NN0 -> ( c e. H |-> ( c ` (/) ) ) : H -1-1-onto-> ( 0 ... k ) )

  proof
    vk
    cv
    #
    cn0
    wcel
    #
    cH
    vc
    cn0
    c1o
    cmap
    co
    #
    c0
    vc
    cv
    #
    cfv
    #
    cmpt
    #
    cH
    cima
    #
    @5
    cH
    cres
    #
    wf1o
    #
    cH
    cc0
    @0
    cfz
    co
    #
    vc
    cH
    @4
    cmpt
    #
    wf1o
    #
    @1
    @2
    cn0
    @5
    wf1
    #
    cH
    @2
    wss
    #
    @8
    @2
    cn0
    @5
    wf1o
    #
    @12
    vc
    cn0
    c1o
    @5
    c0
    df1o2
    nn0ex
    0ex
    @5
    eqid
    #
    mapsnf1o2
    #
    @2
    cn0
    @5
    f1of1
    ax-mp
    @13
    @1
    cH
    vd
    cv
    #
    c1o
    @0
    csn
    cxp
    cle
    cofr
    wbr
    #
    vd
    @2
    crab
    #
    @2
    coe1mul2lem2.h
    @18
    vd
    @2
    ssrab2
    eqsstri
    a1i
    #
    @2
    cn0
    cH
    @5
    f1ores
    sylancr
    @1
    @8
    cH
    @9
    @7
    wf1o
    #
    @11
    @1
    @6
    @9
    cH
    @7
    @1
    @6
    @5
    @5
    ccnv
    @9
    cima
    #
    cima
    #
    @9
    @1
    cH
    @22
    @5
    @1
    @19
    @4
    @9
    wcel
    #
    vc
    @2
    crab
    #
    cH
    @22
    @1
    @19
    c0
    @17
    cfv
    #
    @9
    wcel
    #
    vd
    @2
    crab
    @25
    @1
    @18
    @27
    vd
    @2
    @0
    @17
    coe1mul2lem1
    rabbidva
    @24
    @27
    vc
    vd
    @2
    @3
    @17
    wceq
    @4
    @26
    @9
    c0
    @3
    @17
    fveq1
    eleq1d
    cbvrabv
    syl6eqr
    coe1mul2lem2.h
    vc
    @2
    @4
    @9
    @5
    @15
    mptpreima
    3eqtr4g
    imaeq2d
    @2
    cn0
    @5
    wfo
    #
    @9
    cn0
    wss
    @23
    @9
    wceq
    @14
    @28
    @16
    @2
    cn0
    @5
    f1ofo
    ax-mp
    @0
    fz0ssnn0
    @2
    cn0
    @9
    @5
    foimacnv
    mp2an
    syl6eq
    f1oeq3d
    @1
    @13
    @7
    @10
    wceq
    @21
    @11
    wb
    @20
    vc
    @2
    cH
    @4
    resmpt
    cH
    @9
    @7
    @10
    f1oeq1
    3syl
    bitrd
    mpbid
end
