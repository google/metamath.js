include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "cdif.mm"
include "cpr.mm"
include "cv.mm"
include "wdisj.mm"
include "csn.mm"
include "disjxsn.mm"
include "simpr.mm"
include "eqidd.mm"
include "wb.mm"
include "elex.mm"
include "cvv.mm"
include "0ex.mm"
include "a1i.mm"
include "preqsnd.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "disjeq1d.mm"
include "mpbiri.mm"
include "wne.mm"
include "cin.mm"
include "in0.mm"
include "id.mm"
include "disjprg.mm"
include "syl3anc.mm"
include "pm2.61dane.mm"
include "ad2antlr.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "preq12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "wn.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "difexg.mm"
include "ad2antrr.mm"
include "wss.mm"
include "ssid.mm"
include "ssdifeq0.mm"
include "notbii.mm"
include "nssne2.mm"
include "sylan2br.mm"
include "mpan.mm"
include "pm2.61dan.mm"

theorem disjdifprg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  assert |- ( ( A e. V /\ B e. W ) -> Disj_ x e. { ( B \ A ) , A } x )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    c0
    wceq
    #
    vx
    cB
    cA
    cdif
    #
    cA
    cpr
    #
    vx
    cv
    #
    wdisj
    #
    @2
    @3
    wa
    @7
    vx
    cB
    c0
    cpr
    #
    @6
    wdisj
    #
    @1
    @9
    @0
    @3
    @1
    @9
    cB
    c0
    @1
    cB
    c0
    wceq
    #
    wa
    #
    @9
    vx
    c0
    csn
    #
    @6
    wdisj
    vx
    c0
    @6
    disjxsn
    @11
    vx
    @8
    @12
    @6
    @11
    @8
    @12
    wceq
    #
    @10
    c0
    c0
    wceq
    #
    @1
    @10
    simpr
    @11
    c0
    eqidd
    @1
    @13
    @10
    @14
    wa
    wb
    @10
    @1
    cB
    c0
    c0
    cB
    cW
    elex
    #
    c0
    cvv
    wcel
    #
    @1
    0ex
    a1i
    #
    @17
    preqsnd
    adantr
    mpbir2and
    disjeq1d
    mpbiri
    @1
    cB
    c0
    wne
    #
    wa
    #
    @9
    cB
    c0
    cin
    c0
    wceq
    #
    cB
    in0
    @19
    cB
    cvv
    wcel
    #
    @16
    @18
    @9
    @20
    wb
    @1
    @21
    @18
    @15
    adantr
    @16
    @19
    0ex
    a1i
    @1
    @18
    simpr
    vx
    cB
    c0
    @6
    cB
    c0
    cvv
    @6
    cB
    wceq
    id
    @6
    c0
    wceq
    id
    disjprg
    syl3anc
    mpbiri
    pm2.61dane
    ad2antlr
    @3
    @7
    @9
    wb
    @2
    @3
    vx
    @5
    @8
    @6
    @3
    @4
    cB
    cA
    c0
    @3
    @4
    cB
    c0
    cdif
    cB
    cA
    c0
    cB
    difeq2
    cB
    dif0
    syl6eq
    @3
    id
    preq12d
    disjeq1d
    adantl
    mpbird
    @2
    @3
    wn
    #
    wa
    #
    @7
    @4
    cA
    cin
    #
    c0
    wceq
    #
    cA
    @4
    cin
    @24
    c0
    cA
    @4
    incom
    cA
    cB
    disjdif
    eqtr3i
    @23
    @4
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @4
    cA
    wne
    #
    @7
    @25
    wb
    @1
    @26
    @0
    @22
    cB
    cA
    cW
    difexg
    ad2antlr
    @0
    @27
    @1
    @22
    cA
    cV
    elex
    ad2antrr
    @22
    @28
    @2
    @4
    @4
    wss
    #
    @22
    @28
    @4
    ssid
    @22
    @29
    cA
    @4
    wss
    #
    wn
    @28
    @30
    @3
    cA
    cB
    ssdifeq0
    notbii
    @4
    cA
    @4
    nssne2
    sylan2br
    mpan
    adantl
    vx
    @4
    cA
    @6
    @4
    cA
    cvv
    @6
    @4
    wceq
    id
    @6
    cA
    wceq
    id
    disjprg
    syl3anc
    mpbiri
    pm2.61dan
end
