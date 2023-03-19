include "cxr.mm"
include "wcel.mm"
include "cabs.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cbl.mm"
include "cfv.mm"
include "cv.mm"
include "cc.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cle.mm"
include "w3a.mm"
include "abscl.mm"
include "absge0.mm"
include "jca.mm"
include "adantl.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6rbbr.mm"
include "wb.mm"
include "0re.mm"
include "simpl.mm"
include "elico2.mm"
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
include "wfn.mm"
include "wf.mm"
include "absf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "elpreima.mm"
include "mp1i.mm"
include "cxmt.mm"
include "ccom.mm"
include "cnxmet.mm"
include "eqeltri.mm"
include "elbl.mm"
include "mp3an12.mm"
include "eqrdv.mm"

theorem cnbl0
  let cD: class D
  let cR: class R
  let vx: setvar x
  assume cnblcld.1: |- D = ( abs o. - )


  assert |- ( R e. RR* -> ( `' abs " ( 0 [,) R ) ) = ( 0 ( ball ` D ) R ) )

  proof
    cR
    cxr
    wcel
    #
    vx
    cabs
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc0
    cR
    cD
    cbl
    cfv
    co
    #
    @0
    vx
    cv
    #
    cc
    wcel
    #
    @4
    cabs
    cfv
    #
    @1
    wcel
    #
    wa
    #
    @5
    cc0
    @4
    cD
    co
    #
    cR
    clt
    wbr
    #
    wa
    #
    @4
    @2
    wcel
    #
    @4
    @3
    wcel
    #
    @0
    @5
    @7
    @10
    @0
    @5
    wa
    #
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cR
    clt
    wbr
    #
    w3a
    #
    @17
    @7
    @10
    @14
    @17
    @15
    @16
    wa
    #
    @17
    wa
    @18
    @14
    @19
    @17
    @5
    @19
    @0
    @5
    @15
    @16
    @4
    abscl
    @4
    absge0
    jca
    adantl
    biantrurd
    @15
    @16
    @17
    df-3an
    syl6rbbr
    @14
    cc0
    cr
    wcel
    @0
    @7
    @18
    wb
    0re
    @0
    @5
    simpl
    cc0
    cR
    @6
    elico2
    sylancr
    @14
    @9
    @6
    cR
    clt
    @5
    @9
    @6
    wceq
    @0
    @5
    @9
    @4
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    cc0
    cc
    wcel
    #
    @5
    @9
    @21
    wceq
    0cn
    @22
    @5
    wa
    @9
    cc0
    @4
    cmin
    co
    cabs
    cfv
    @21
    cc0
    @4
    cD
    cnblcld.1
    cnmetdval
    cc0
    @4
    abssub
    eqtrd
    mpan
    @5
    @20
    @4
    cabs
    @4
    subid1
    fveq2d
    eqtrd
    adantl
    breq1d
    3bitr4d
    pm5.32da
    cabs
    cc
    wfn
    #
    @12
    @8
    wb
    @0
    cc
    cr
    cabs
    wf
    @23
    absf
    cc
    cr
    cabs
    ffn
    ax-mp
    cc
    @4
    @1
    cabs
    elpreima
    mp1i
    cD
    cc
    cxmt
    cfv
    #
    wcel
    @22
    @0
    @13
    @11
    wb
    cD
    cabs
    cmin
    ccom
    @24
    cnblcld.1
    cnxmet
    eqeltri
    0cn
    @4
    cD
    cc0
    cR
    cc
    elbl
    mp3an12
    3bitr4d
    eqrdv
end
