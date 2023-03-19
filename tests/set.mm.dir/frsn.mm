include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wfr.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "snprc.mm"
include "fr0.mm"
include "freq2.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "adantl.mm"
include "brrelex.mm"
include "stoic1a.mm"
include "2thd.mm"
include "ex.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wss.mm"
include "wne.mm"
include "wi.mm"
include "wal.mm"
include "df-fr.mm"
include "wo.mm"
include "sssn.mm"
include "neor.mm"
include "sylbb.mm"
include "imp.mm"
include "eqimss.mm"
include "snnzg.mm"
include "neeq1.mm"
include "syl5ibrcom.mm"
include "jca.mm"
include "impbida.mm"
include "imbi1d.mm"
include "albidv.mm"
include "snex.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "ceqsalv.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexsng.mm"
include "breq1.mm"
include "ralsng.mm"
include "3bitrd.mm"
include "pm2.61d2.mm"

theorem frsn
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel R -> ( R Fr { A } <-> -. A R A ) )

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
    wfr
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
    @2
    c0
    wceq
    #
    @3
    cA
    snprc
    @8
    @3
    c0
    cR
    wfr
    cR
    fr0
    @2
    c0
    cR
    freq2
    mpbiri
    sylbi
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
    @1
    @3
    vz
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vz
    @2
    wral
    #
    vy
    @2
    wrex
    #
    @9
    cA
    cR
    wbr
    #
    wn
    #
    vz
    @2
    wral
    #
    @5
    @3
    vx
    cv
    #
    @2
    wss
    #
    @18
    c0
    wne
    #
    wa
    #
    @12
    vz
    @18
    wral
    #
    vy
    @18
    wrex
    #
    wi
    #
    vx
    wal
    #
    @1
    @14
    vx
    vy
    vz
    @2
    cR
    df-fr
    @1
    @25
    @18
    @2
    wceq
    #
    @23
    wi
    #
    vx
    wal
    @14
    @1
    @24
    @27
    vx
    @1
    @21
    @26
    @23
    @1
    @21
    @26
    @21
    @26
    @1
    @19
    @20
    @26
    @19
    @18
    c0
    wceq
    @26
    wo
    @20
    @26
    wi
    @18
    cA
    sssn
    @26
    @18
    c0
    neor
    sylbb
    imp
    adantl
    @1
    @26
    wa
    @19
    @20
    @26
    @19
    @1
    @18
    @2
    eqimss
    adantl
    @1
    @26
    @20
    @1
    @20
    @26
    @2
    c0
    wne
    cA
    cvv
    snnzg
    @18
    @2
    c0
    neeq1
    syl5ibrcom
    imp
    jca
    impbida
    imbi1d
    albidv
    @23
    @14
    vx
    @2
    cA
    snex
    @22
    @13
    vy
    @18
    @2
    @12
    vz
    @18
    @2
    raleq
    rexeqbi1dv
    ceqsalv
    syl6bb
    syl5bb
    @13
    @17
    vy
    cA
    cvv
    @10
    cA
    wceq
    #
    @12
    @16
    vz
    @2
    @28
    @11
    @15
    @10
    cA
    @9
    cR
    breq2
    notbid
    ralbidv
    rexsng
    @16
    @5
    vz
    cA
    cvv
    @9
    cA
    wceq
    @15
    @4
    @9
    cA
    cA
    cR
    breq1
    notbid
    ralsng
    3bitrd
    pm2.61d2
end
