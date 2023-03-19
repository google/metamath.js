include "wcel.mm"
include "cvv.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantr.mm"
include "intex.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "wb.mm"
include "elfi.mm"
include "wn.mm"
include "vprc.mm"
include "elsni.mm"
include "inteqd.mm"
include "int0.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "simpll.mm"
include "eqeltrrd.mm"
include "nsyl3.mm"
include "biantrud.mm"
include "eldif.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "rexbidv2.mm"
include "bitrd.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem elfi2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint V x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint W x
  assert |- ( B e. V -> ( A e. ( fi ` B ) <-> E. x e. ( ( ~P B i^i Fin ) \ { (/) } ) A = |^| x ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    cfi
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    cint
    #
    wceq
    #
    vx
    cB
    cpw
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    wrex
    #
    @3
    @1
    wi
    @0
    cA
    @2
    elex
    a1i
    @10
    @1
    wi
    @0
    @6
    @1
    vx
    @9
    @4
    @9
    wcel
    #
    @6
    wa
    #
    cA
    @5
    cvv
    @11
    @6
    simpr
    @12
    @4
    c0
    wne
    #
    @5
    cvv
    wcel
    #
    @11
    @13
    @6
    @4
    @7
    c0
    eldifsni
    adantr
    @4
    intex
    sylib
    eqeltrd
    rexlimiva
    a1i
    @1
    @0
    @3
    @10
    wb
    @1
    @0
    wa
    #
    @3
    @6
    vx
    @7
    wrex
    @10
    vx
    cA
    cB
    cvv
    cV
    elfi
    @15
    @6
    @6
    vx
    @7
    @9
    @15
    @6
    @4
    @7
    wcel
    #
    wa
    @6
    @11
    wa
    @16
    @6
    wa
    @12
    @15
    @6
    @16
    @11
    @15
    @6
    wa
    #
    @16
    @16
    @4
    @8
    wcel
    #
    wn
    #
    wa
    @11
    @17
    @19
    @16
    @18
    @14
    @17
    @18
    @14
    cvv
    cvv
    wcel
    vprc
    @18
    @5
    cvv
    cvv
    @18
    @5
    c0
    cint
    cvv
    @18
    @4
    c0
    @4
    c0
    elsni
    inteqd
    int0
    syl6eq
    eleq1d
    mtbiri
    @17
    cA
    @5
    cvv
    @15
    @6
    simpr
    @1
    @0
    @6
    simpll
    eqeltrrd
    nsyl3
    biantrud
    @4
    @7
    @8
    eldif
    syl6bbr
    pm5.32da
    @16
    @6
    ancom
    @11
    @6
    ancom
    3bitr4g
    rexbidv2
    bitrd
    expcom
    pm5.21ndd
end
