include "cqs.mm"
include "wss.mm"
include "wa.mm"
include "cin.mm"
include "cuni.mm"
include "uniin.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "eluni2.mm"
include "anbi12i.mm"
include "elin.mm"
include "reeanv.mm"
include "3bitr4i.mm"
include "w3a.mm"
include "simp3l.mm"
include "simp2l.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "inelcm.mm"
include "3ad2ant3.mm"
include "wer.mm"
include "simp1l.mm"
include "sseldd.mm"
include "simp1r.mm"
include "simp2r.mm"
include "qsdisj.mm"
include "ord.mm"
include "necon1ad.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "elind.mm"
include "elunii.mm"
include "syl2anc.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem uniinqs
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  assume uniinqs.1: |- R Er X


  assert |- ( ( B C_ ( A /. R ) /\ C C_ ( A /. R ) ) -> U. ( B i^i C ) = ( U. B i^i U. C ) )

  proof
    cB
    cA
    cR
    cqs
    #
    wss
    #
    cC
    @0
    wss
    #
    wa
    #
    cB
    cC
    cin
    #
    cuni
    #
    cB
    cuni
    #
    cC
    cuni
    #
    cin
    #
    @5
    @8
    wss
    @3
    cB
    cC
    uniin
    a1i
    @3
    vx
    @8
    @5
    vx
    cv
    #
    @8
    wcel
    #
    @9
    vb
    cv
    #
    wcel
    #
    @9
    vc
    cv
    #
    wcel
    #
    wa
    #
    vc
    cC
    wrex
    vb
    cB
    wrex
    #
    @3
    @9
    @5
    wcel
    #
    @9
    @6
    wcel
    #
    @9
    @7
    wcel
    #
    wa
    @12
    vb
    cB
    wrex
    #
    @14
    vc
    cC
    wrex
    #
    wa
    @10
    @16
    @18
    @20
    @19
    @21
    vb
    @9
    cB
    eluni2
    vc
    @9
    cC
    eluni2
    anbi12i
    @9
    @6
    @7
    elin
    @12
    @14
    vb
    vc
    cB
    cC
    reeanv
    3bitr4i
    @3
    @15
    @17
    vb
    vc
    cB
    cC
    @3
    @11
    cB
    wcel
    #
    @13
    cC
    wcel
    #
    wa
    #
    @15
    @17
    @3
    @24
    @15
    w3a
    #
    @12
    @11
    @4
    wcel
    @17
    @3
    @24
    @12
    @14
    simp3l
    @25
    cB
    cC
    @11
    @3
    @22
    @23
    @15
    simp2l
    #
    @25
    @11
    @13
    cC
    @25
    @11
    @13
    cin
    #
    c0
    wne
    #
    @11
    @13
    wceq
    #
    @15
    @3
    @28
    @24
    @9
    @11
    @13
    inelcm
    3ad2ant3
    @25
    @29
    @27
    c0
    @25
    @29
    @27
    c0
    wceq
    @25
    cA
    @11
    @13
    cR
    cX
    cX
    cR
    wer
    @25
    uniinqs.1
    a1i
    @25
    cB
    @0
    @11
    @1
    @2
    @24
    @15
    simp1l
    @26
    sseldd
    @25
    cC
    @0
    @13
    @1
    @2
    @24
    @15
    simp1r
    @3
    @22
    @23
    @15
    simp2r
    #
    sseldd
    qsdisj
    ord
    necon1ad
    mpd
    @30
    eqeltrd
    elind
    @9
    @11
    @4
    elunii
    syl2anc
    3expia
    rexlimdvva
    syl5bi
    ssrdv
    eqssd
end
