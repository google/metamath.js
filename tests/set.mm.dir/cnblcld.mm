include "cxr.mm"
include "wcel.mm"
include "cabs.mm"
include "ccnv.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "cfv.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "w3a.mm"
include "abscl.mm"
include "rexrd.mm"
include "absge0.mm"
include "jca.mm"
include "adantl.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6rbbr.mm"
include "0xr.mm"
include "simpl.mm"
include "elicc1.mm"
include "sylancr.mm"
include "wceq.mm"
include "cmin.mm"
include "0cn.mm"
include "cnmetdval.mm"
include "abssub.mm"
include "eqtrd.mm"
include "mpan.mm"
include "subid1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"

theorem cnblcld
  let vx: setvar x
  let cD: class D
  let cR: class R
  assume cnblcld.1: |- D = ( abs o. - )

  disjoint D x
  disjoint R x
  assert |- ( R e. RR* -> ( `' abs " ( 0 [,] R ) ) = { x e. CC | ( 0 D x ) <_ R } )

  proof
    cR
    cxr
    wcel
    #
    cabs
    ccnv
    cc0
    cR
    cicc
    co
    #
    cima
    #
    vx
    cv
    #
    cc
    wcel
    #
    cc0
    @3
    cD
    co
    #
    cR
    cle
    wbr
    #
    wa
    #
    vx
    cab
    @6
    vx
    cc
    crab
    @0
    @7
    vx
    @2
    @3
    @2
    wcel
    #
    @4
    @3
    cabs
    cfv
    #
    @1
    wcel
    #
    wa
    #
    @0
    @7
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @8
    @11
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @3
    @1
    cabs
    elpreima
    mp2b
    @0
    @4
    @10
    @6
    @0
    @4
    wa
    #
    @9
    cxr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    @9
    cR
    cle
    wbr
    #
    w3a
    #
    @15
    @10
    @6
    @12
    @15
    @13
    @14
    wa
    #
    @15
    wa
    @16
    @12
    @17
    @15
    @4
    @17
    @0
    @4
    @13
    @14
    @4
    @9
    @3
    abscl
    rexrd
    @3
    absge0
    jca
    adantl
    biantrurd
    @13
    @14
    @15
    df-3an
    syl6rbbr
    @12
    cc0
    cxr
    wcel
    @0
    @10
    @16
    wb
    0xr
    @0
    @4
    simpl
    cc0
    cR
    @9
    elicc1
    sylancr
    @12
    @5
    @9
    cR
    cle
    @4
    @5
    @9
    wceq
    @0
    @4
    @5
    @3
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    cc0
    cc
    wcel
    #
    @4
    @5
    @19
    wceq
    0cn
    @20
    @4
    wa
    @5
    cc0
    @3
    cmin
    co
    cabs
    cfv
    @19
    cc0
    @3
    cD
    cnblcld.1
    cnmetdval
    cc0
    @3
    abssub
    eqtrd
    mpan
    @4
    @18
    @3
    cabs
    @3
    subid1
    fveq2d
    eqtrd
    adantl
    breq1d
    3bitr4d
    pm5.32da
    syl5bb
    abbi2dv
    @6
    vx
    cc
    df-rab
    syl6eqr
end
