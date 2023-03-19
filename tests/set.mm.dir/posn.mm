include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wpo.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "wa.mm"
include "c0.mm"
include "po0.mm"
include "wceq.mm"
include "snprc.mm"
include "poeq2.mm"
include "sylbi.mm"
include "mpbiri.mm"
include "adantl.mm"
include "brrelex.mm"
include "stoic1a.mm"
include "2thd.mm"
include "ex.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "df-po.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi12d.mm"
include "ralsng.mm"
include "ralbidv.mm"
include "simpl.mm"
include "syl5ib.mm"
include "biantrud.mm"
include "bicomd.mm"
include "bitrd.mm"
include "breq12.mm"
include "anidms.mm"
include "notbid.mm"
include "syl5bb.mm"
include "pm2.61d2.mm"

theorem posn
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel R -> ( R Po { A } <-> -. A R A ) )

  proof
    cR
    wrel
    #
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cR
    wpo
    #
    cA
    cA
    cR
    wbr
    #
    wn
    #
    wb
    #
    @0
    @1
    wn
    #
    @6
    @0
    @7
    wa
    @3
    @5
    @7
    @3
    @0
    @7
    @3
    c0
    cR
    wpo
    #
    cR
    po0
    @7
    @2
    c0
    wceq
    @3
    @8
    wb
    cA
    snprc
    @2
    c0
    cR
    poeq2
    sylbi
    mpbiri
    adantl
    @0
    @4
    @1
    cA
    cA
    cR
    brrelex
    stoic1a
    2thd
    ex
    @3
    vx
    cv
    #
    @9
    cR
    wbr
    #
    wn
    #
    @9
    vy
    cv
    #
    cR
    wbr
    #
    @12
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @9
    @14
    cR
    wbr
    #
    wi
    #
    wa
    #
    vz
    @2
    wral
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    @1
    @5
    vx
    vy
    vz
    @2
    cR
    df-po
    @1
    @22
    @11
    vx
    @2
    wral
    @5
    @1
    @21
    @11
    vx
    @2
    @1
    @21
    @11
    @13
    @12
    cA
    cR
    wbr
    #
    wa
    #
    @9
    cA
    cR
    wbr
    #
    wi
    #
    wa
    #
    vy
    @2
    wral
    @11
    @1
    @20
    @27
    vy
    @2
    @19
    @27
    vz
    cA
    cvv
    @14
    cA
    wceq
    #
    @18
    @26
    @11
    @28
    @16
    @24
    @17
    @25
    @28
    @15
    @23
    @13
    @14
    cA
    @12
    cR
    breq2
    anbi2d
    @14
    cA
    @9
    cR
    breq2
    imbi12d
    anbi2d
    ralsng
    ralbidv
    @27
    @11
    vy
    cA
    cvv
    @12
    cA
    wceq
    #
    @11
    @27
    @29
    @26
    @11
    @24
    @13
    @29
    @25
    @13
    @23
    simpl
    @12
    cA
    @9
    cR
    breq2
    syl5ib
    biantrud
    bicomd
    ralsng
    bitrd
    ralbidv
    @11
    @5
    vx
    cA
    cvv
    @9
    cA
    wceq
    #
    @10
    @4
    @30
    @10
    @4
    wb
    @9
    cA
    @9
    cA
    cR
    breq12
    anidms
    notbid
    ralsng
    bitrd
    syl5bb
    pm2.61d2
end
