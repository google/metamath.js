include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cdif.mm"
include "cmnf.mm"
include "cico.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wo.mm"
include "biortn.mm"
include "wb.mm"
include "pnfge.mm"
include "notnotd.mm"
include "biorf.mm"
include "syl.mm"
include "orcom.mm"
include "syl6bbr.mm"
include "w3a.mm"
include "w3o.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "notbii.mm"
include "3ianor.mm"
include "3orass.mm"
include "3bitri.mm"
include "a1i.mm"
include "3bitr4rd.mm"
include "xrltnle.mm"
include "mpan2.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "eldif.mm"
include "3anass.mm"
include "mnfxr.mm"
include "elico1.mm"
include "mnfle.mm"
include "biantrurd.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem xrdifh
  let cA: class A
  let vx: setvar x
  assume xrdifh.1: |- A e. RR*


  assert |- ( RR* \ ( A [,] +oo ) ) = ( -oo [,) A )

  proof
    vx
    cxr
    cA
    cpnf
    cicc
    co
    #
    cdif
    #
    cmnf
    cA
    cico
    co
    #
    vx
    cv
    #
    cxr
    wcel
    #
    @3
    @0
    wcel
    #
    wn
    #
    wa
    @4
    @3
    cA
    clt
    wbr
    #
    wa
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    #
    @4
    @6
    @7
    @4
    @6
    cA
    @3
    cle
    wbr
    #
    wn
    #
    @7
    @4
    @11
    @3
    cpnf
    cle
    wbr
    #
    wn
    #
    wo
    #
    @4
    wn
    #
    @14
    wo
    #
    @11
    @6
    @4
    @14
    biortn
    @4
    @11
    @13
    @11
    wo
    #
    @14
    @4
    @13
    wn
    @11
    @17
    wb
    @4
    @12
    @3
    pnfge
    notnotd
    @13
    @11
    biorf
    syl
    @11
    @13
    orcom
    syl6bbr
    @6
    @16
    wb
    @4
    @6
    @4
    @10
    @12
    w3a
    #
    wn
    @15
    @11
    @13
    w3o
    @16
    @5
    @18
    cA
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    @5
    @18
    wb
    xrdifh.1
    pnfxr
    cA
    cpnf
    @3
    elicc1
    mp2an
    notbii
    @4
    @10
    @12
    3ianor
    @15
    @11
    @13
    3orass
    3bitri
    a1i
    3bitr4rd
    @4
    @19
    @7
    @11
    wb
    xrdifh.1
    @3
    cA
    xrltnle
    mpan2
    bitr4d
    pm5.32i
    @3
    cxr
    @0
    eldif
    @4
    cmnf
    @3
    cle
    wbr
    #
    @7
    w3a
    #
    @4
    @20
    @7
    wa
    #
    wa
    @9
    @8
    @4
    @20
    @7
    3anass
    cmnf
    cxr
    wcel
    @19
    @9
    @21
    wb
    mnfxr
    xrdifh.1
    cmnf
    cA
    @3
    elico1
    mp2an
    @4
    @7
    @22
    @4
    @20
    @7
    @3
    mnfle
    biantrurd
    pm5.32i
    3bitr4i
    3bitr4i
    eqriv
end
