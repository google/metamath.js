include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "cdom.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wex.mm"
include "sdom0.mm"
include "breq2.mm"
include "mtbiri.mm"
include "con2i.mm"
include "neq0.mm"
include "sylib.mm"
include "wa.mm"
include "cdif.mm"
include "domdifsn.mm"
include "adantr.mm"
include "cvv.mm"
include "cen.mm"
include "vex.mm"
include "en2sn.mm"
include "mpan2.mm"
include "endom.mm"
include "syl.mm"
include "snprc.mm"
include "biimpi.mm"
include "snex.mm"
include "0dom.mm"
include "syl6eqbr.mm"
include "pm2.61i.mm"
include "cin.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "undom.mm"
include "sylancl.mm"
include "uncom.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "undif.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "exlimddv.mm"

theorem domunsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z


  assert |- ( A ~< B -> ( A u. { C } ) ~<_ B )

  proof
    cA
    cB
    csdm
    wbr
    #
    vz
    cv
    #
    cB
    wcel
    #
    cA
    cC
    csn
    #
    cun
    #
    cB
    cdom
    wbr
    vz
    @0
    cB
    c0
    wceq
    #
    wn
    @2
    vz
    wex
    @5
    @0
    @5
    @0
    cA
    c0
    csdm
    wbr
    cA
    sdom0
    cB
    c0
    cA
    csdm
    breq2
    mtbiri
    con2i
    vz
    cB
    neq0
    sylib
    @0
    @2
    wa
    #
    @4
    cB
    @1
    csn
    #
    cdif
    #
    @7
    cun
    #
    cB
    cdom
    @6
    cA
    @8
    cdom
    wbr
    #
    @3
    @7
    cdom
    wbr
    #
    @4
    @9
    cdom
    wbr
    #
    @0
    @10
    @2
    cA
    cB
    @1
    domdifsn
    adantr
    cC
    cvv
    wcel
    #
    @11
    @13
    @3
    @7
    cen
    wbr
    #
    @11
    @13
    @1
    cvv
    wcel
    @14
    vz
    vex
    cC
    @1
    cvv
    cvv
    en2sn
    mpan2
    @3
    @7
    endom
    syl
    @13
    wn
    #
    @3
    c0
    @7
    cdom
    @15
    @3
    c0
    wceq
    cC
    snprc
    biimpi
    @7
    @1
    snex
    0dom
    syl6eqbr
    pm2.61i
    @10
    @11
    wa
    @8
    @7
    cin
    #
    c0
    wceq
    @12
    @16
    @7
    @8
    cin
    c0
    @8
    @7
    incom
    @7
    cB
    disjdif
    eqtri
    cA
    @8
    @3
    @7
    undom
    mpan2
    sylancl
    @6
    @9
    @7
    @8
    cun
    #
    cB
    @8
    @7
    uncom
    @6
    @7
    cB
    wss
    @17
    cB
    wceq
    @6
    @1
    cB
    @0
    @2
    simpr
    snssd
    @7
    cB
    undif
    sylib
    syl5eq
    breqtrd
    exlimddv
end
