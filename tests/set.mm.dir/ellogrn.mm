include "cim.mm"
include "ccnv.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "wcel.mm"
include "cc.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wa.mm"
include "clog.mm"
include "crn.mm"
include "w3a.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "imf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "imcl.mm"
include "biantrurd.mm"
include "cxr.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioc2.mm"
include "mp2an.mm"
include "3anass.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "logrn.mm"
include "eleq2i.mm"
include "3bitr4i.mm"

theorem ellogrn
  let cA: class A


  assert |- ( A e. ran log <-> ( A e. CC /\ -u _pi < ( Im ` A ) /\ ( Im ` A ) <_ _pi ) )

  proof
    cA
    cim
    ccnv
    cpi
    cneg
    #
    cpi
    cioc
    co
    #
    cima
    #
    wcel
    #
    cA
    cc
    wcel
    #
    @0
    cA
    cim
    cfv
    #
    clt
    wbr
    #
    @5
    cpi
    cle
    wbr
    #
    wa
    #
    wa
    #
    cA
    clog
    crn
    #
    wcel
    @4
    @6
    @7
    w3a
    @3
    @4
    @5
    @1
    wcel
    #
    wa
    #
    @9
    cc
    cr
    cim
    wf
    cim
    cc
    wfn
    @3
    @12
    wb
    imf
    cc
    cr
    cim
    ffn
    cc
    cA
    @1
    cim
    elpreima
    mp2b
    @4
    @11
    @8
    @4
    @8
    @5
    cr
    wcel
    #
    @8
    wa
    #
    @11
    @4
    @13
    @8
    cA
    imcl
    biantrurd
    @11
    @13
    @6
    @7
    w3a
    #
    @14
    @0
    cxr
    wcel
    cpi
    cr
    wcel
    @11
    @15
    wb
    @0
    cpi
    pire
    renegcli
    rexri
    pire
    @0
    cpi
    @5
    elioc2
    mp2an
    @13
    @6
    @7
    3anass
    bitri
    syl6rbbr
    pm5.32i
    bitri
    @10
    @2
    cA
    logrn
    eleq2i
    @4
    @6
    @7
    3anass
    3bitr4i
end
