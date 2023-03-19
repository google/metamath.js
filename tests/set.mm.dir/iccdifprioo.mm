include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "cpr.mm"
include "cdif.mm"
include "cioo.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "prunioo.mm"
include "eqcomd.mm"
include "difeq1d.mm"
include "difun2.mm"
include "cin.mm"
include "c0.mm"
include "iooinlbub.mm"
include "disj3.mm"
include "mpbi.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "3expa.mm"
include "wn.mm"
include "wss.mm"
include "difssd.mm"
include "clt.mm"
include "simpr.mm"
include "wb.mm"
include "xrlenlt.mm"
include "adantr.mm"
include "mtbid.mm"
include "notnotrd.mm"
include "icc0.mm"
include "mpbird.mm"
include "sseqtrd.mm"
include "ss0.mm"
include "syl.mm"
include "simplr.mm"
include "simpll.mm"
include "xrltled.mm"
include "ioo0.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem iccdifprioo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( ( A [,] B ) \ { A , B } ) = ( A (,) B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cicc
    co
    #
    cA
    cB
    cpr
    #
    cdif
    #
    cA
    cB
    cioo
    co
    #
    wceq
    #
    @0
    @1
    @3
    @8
    @0
    @1
    @3
    w3a
    #
    @6
    @7
    @5
    cun
    #
    @5
    cdif
    #
    @7
    @9
    @4
    @10
    @5
    @9
    @10
    @4
    cA
    cB
    prunioo
    eqcomd
    difeq1d
    @11
    @7
    @5
    cdif
    #
    @7
    @7
    @5
    difun2
    @7
    @5
    cin
    c0
    wceq
    @7
    @12
    wceq
    cA
    cB
    iooinlbub
    @7
    @5
    disj3
    mpbi
    eqtr4i
    syl6eq
    3expa
    @2
    @3
    wn
    #
    wa
    #
    @6
    c0
    @7
    @14
    @6
    c0
    wss
    @6
    c0
    wceq
    @14
    @6
    @4
    c0
    @14
    @4
    @5
    difssd
    @14
    @4
    c0
    wceq
    #
    cB
    cA
    clt
    wbr
    #
    @14
    @16
    @14
    @3
    @16
    wn
    #
    @2
    @13
    simpr
    @2
    @3
    @17
    wb
    @13
    cA
    cB
    xrlenlt
    adantr
    mtbid
    notnotrd
    #
    @2
    @15
    @16
    wb
    @13
    cA
    cB
    icc0
    adantr
    mpbird
    sseqtrd
    @6
    ss0
    syl
    @14
    @7
    c0
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    @14
    cB
    cA
    @0
    @1
    @13
    simplr
    @0
    @1
    @13
    simpll
    @18
    xrltled
    @2
    @19
    @20
    wb
    @13
    cA
    cB
    ioo0
    adantr
    mpbird
    eqtr4d
    pm2.61dan
end
