include "ctop.mm"
include "wcel.mm"
include "clp.mm"
include "cfv.mm"
include "wa.mm"
include "csn.mm"
include "wn.mm"
include "wss.mm"
include "ssid.mm"
include "lpss.mm"
include "mpan2.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "cdif.mm"
include "ccl.mm"
include "cnt.mm"
include "wb.mm"
include "simpl.mm"
include "islp.mm"
include "sylancl.mm"
include "wceq.mm"
include "snssi.mm"
include "clsdif.mm"
include "sylan2.mm"
include "eleq2d.mm"
include "eldif.mm"
include "baib.mm"
include "adantl.mm"
include "ntrss2.mm"
include "adantr.mm"
include "eqssd.mm"
include "ntropn.mm"
include "eqeltrd.mm"
include "snidg.mm"
include "ad2antlr.mm"
include "isopn3i.mm"
include "adantlr.mm"
include "eleqtrrd.mm"
include "impbida.mm"
include "notbid.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "pm5.32da.mm"

theorem maxlp
  let cP: class P
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( J e. Top -> ( P e. ( ( limPt ` J ) ` X ) <-> ( P e. X /\ -. { P } e. J ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cP
    cX
    cJ
    clp
    cfv
    cfv
    #
    wcel
    #
    cP
    cX
    wcel
    #
    @2
    wa
    @3
    cP
    csn
    #
    cJ
    wcel
    #
    wn
    #
    wa
    @0
    @2
    @3
    @0
    @1
    cX
    cP
    @0
    cX
    cX
    wss
    #
    @1
    cX
    wss
    cX
    ssid
    #
    cX
    cJ
    cX
    lpfval.1
    lpss
    mpan2
    sseld
    pm4.71rd
    @0
    @3
    @2
    @6
    @0
    @3
    wa
    #
    @2
    cP
    cX
    @4
    cdif
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cP
    cX
    @4
    cJ
    cnt
    cfv
    cfv
    #
    cdif
    #
    wcel
    #
    @6
    @9
    @0
    @7
    @2
    @11
    wb
    @0
    @3
    simpl
    @8
    cP
    cX
    cJ
    cX
    lpfval.1
    islp
    sylancl
    @9
    @10
    @13
    cP
    @3
    @0
    @4
    cX
    wss
    #
    @10
    @13
    wceq
    cP
    cX
    snssi
    #
    @4
    cJ
    cX
    lpfval.1
    clsdif
    sylan2
    eleq2d
    @9
    @14
    cP
    @12
    wcel
    #
    wn
    #
    @6
    @3
    @14
    @18
    wb
    @0
    @14
    @3
    @18
    cP
    cX
    @12
    eldif
    baib
    adantl
    @9
    @17
    @5
    @9
    @17
    @5
    @9
    @17
    wa
    #
    @4
    @12
    cJ
    @19
    @4
    @12
    @17
    @4
    @12
    wss
    @9
    cP
    @12
    snssi
    adantl
    @9
    @12
    @4
    wss
    #
    @17
    @3
    @0
    @15
    @20
    @16
    @4
    cJ
    cX
    lpfval.1
    ntrss2
    sylan2
    adantr
    eqssd
    @9
    @12
    cJ
    wcel
    #
    @17
    @3
    @0
    @15
    @21
    @16
    @4
    cJ
    cX
    lpfval.1
    ntropn
    sylan2
    adantr
    eqeltrd
    @9
    @5
    wa
    cP
    @4
    @12
    @3
    cP
    @4
    wcel
    @0
    @5
    cP
    cX
    snidg
    ad2antlr
    @0
    @5
    @12
    @4
    wceq
    @3
    @4
    cJ
    isopn3i
    adantlr
    eleqtrrd
    impbida
    notbid
    bitrd
    3bitrd
    pm5.32da
    bitrd
end
