include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cxr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cpnf.mm"
include "cmeas.mm"
include "domprobmeas.mm"
include "measvxrge0.mm"
include "sylan.mm"
include "elxrge0.mm"
include "sylib.mm"
include "cuni.mm"
include "adantr.mm"
include "simpr.mm"
include "csiga.mm"
include "crn.mm"
include "measbase.mm"
include "unielsiga.mm"
include "3syl.mm"
include "wss.mm"
include "elssuni.mm"
include "adantl.mm"
include "measssd.mm"
include "wb.mm"
include "probtot.mm"
include "breq2d.mm"
include "mpbid.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "elicc1.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem prob01
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prob /\ A e. dom P ) -> ( P ` A ) e. ( 0 [,] 1 ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cP
    cfv
    #
    cxr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    cle
    wbr
    #
    w3a
    #
    @4
    cc0
    c1
    cicc
    co
    wcel
    #
    @3
    @5
    @6
    wa
    #
    @7
    @8
    @3
    @4
    cc0
    cpnf
    cicc
    co
    wcel
    #
    @10
    @0
    cP
    @1
    cmeas
    cfv
    wcel
    #
    @2
    @11
    cP
    domprobmeas
    #
    cA
    @1
    cP
    measvxrge0
    sylan
    @4
    elxrge0
    sylib
    @3
    @4
    @1
    cuni
    #
    cP
    cfv
    #
    cle
    wbr
    #
    @7
    @3
    cA
    @14
    @1
    cP
    @0
    @12
    @2
    @13
    adantr
    #
    @0
    @2
    simpr
    @3
    @12
    @1
    csiga
    crn
    cuni
    wcel
    @14
    @1
    wcel
    @17
    @1
    cP
    measbase
    @1
    unielsiga
    3syl
    @2
    cA
    @14
    wss
    @0
    cA
    @1
    elssuni
    adantl
    measssd
    @0
    @16
    @7
    wb
    @2
    @0
    @15
    c1
    @4
    cle
    cP
    probtot
    breq2d
    adantr
    mpbid
    @5
    @6
    @7
    df-3an
    sylanbrc
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @9
    @8
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    @4
    elicc1
    mp2an
    sylibr
end
