include "cat.mm"
include "wcel.mm"
include "ccm.mm"
include "wbr.mm"
include "wa.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wn.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cch.mm"
include "atelch.mm"
include "c0h.mm"
include "choccli.mm"
include "chincl.mm"
include "mpan.mm"
include "chj0.mm"
include "syl.mm"
include "incom.mm"
include "syl6eq.mm"
include "h0elch.mm"
include "chjcom.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "chocini.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "w3a.mm"
include "cmidi.mm"
include "cmcm2ii.mm"
include "fh2.mm"
include "mpanr1.mm"
include "mp3anl2.mm"
include "mpanl1.mm"
include "eqtr4d.mm"
include "sylan.mm"
include "atoml2i.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "wb.mm"
include "atssma.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "ex.mm"
include "orrd.mm"

theorem atordi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cC: class C
  assume atoml.1: |- A e. CH


  assert |- ( ( B e. HAtoms /\ A C_H B ) -> ( B C_ A \/ B C_ ( _|_ ` A ) ) )

  proof
    cB
    cat
    wcel
    #
    cA
    cB
    ccm
    wbr
    #
    wa
    #
    cB
    cA
    wss
    #
    cB
    cA
    cort
    cfv
    #
    wss
    #
    @2
    @3
    wn
    #
    @5
    @2
    @6
    wa
    #
    @5
    cB
    @4
    cin
    #
    cat
    wcel
    #
    @7
    @8
    cA
    cB
    chj
    co
    #
    @4
    cin
    #
    cat
    @2
    @8
    @11
    wceq
    @6
    @2
    @8
    @4
    @10
    cin
    #
    @11
    @0
    cB
    cch
    wcel
    #
    @1
    @8
    @12
    wceq
    cB
    atelch
    @13
    @1
    wa
    @8
    @4
    cA
    cin
    #
    @4
    cB
    cin
    #
    chj
    co
    #
    @12
    @13
    @8
    @16
    wceq
    @1
    @13
    @8
    c0h
    @15
    chj
    co
    #
    @16
    @13
    @15
    c0h
    chj
    co
    #
    @8
    @17
    @13
    @18
    @15
    @8
    @13
    @15
    cch
    wcel
    #
    @18
    @15
    wceq
    @4
    cch
    wcel
    #
    @13
    @19
    cA
    atoml.1
    choccli
    #
    @4
    cB
    chincl
    mpan
    #
    @15
    chj0
    syl
    @4
    cB
    incom
    syl6eq
    @13
    @19
    c0h
    cch
    wcel
    @18
    @17
    wceq
    @22
    h0elch
    @15
    c0h
    chjcom
    sylancl
    eqtr3d
    @14
    c0h
    @15
    chj
    @14
    cA
    @4
    cin
    c0h
    @4
    cA
    incom
    cA
    atoml.1
    chocini
    eqtri
    oveq1i
    syl6eqr
    adantr
    @20
    @13
    @1
    @12
    @16
    wceq
    #
    @21
    @20
    cA
    cch
    wcel
    #
    @13
    @1
    @23
    atoml.1
    @20
    @24
    @13
    w3a
    cA
    @4
    ccm
    wbr
    @1
    @23
    cA
    cA
    atoml.1
    atoml.1
    cA
    atoml.1
    cmidi
    cmcm2ii
    @4
    cA
    cB
    fh2
    mpanr1
    mp3anl2
    mpanl1
    eqtr4d
    sylan
    @4
    @10
    incom
    syl6eq
    adantr
    @0
    @6
    @11
    cat
    wcel
    @1
    cA
    cB
    atoml.1
    atoml2i
    adantlr
    eqeltrd
    @0
    @5
    @9
    wb
    #
    @1
    @6
    @0
    @20
    @25
    @21
    cB
    @4
    atssma
    mpan2
    ad2antrr
    mpbird
    ex
    orrd
end
