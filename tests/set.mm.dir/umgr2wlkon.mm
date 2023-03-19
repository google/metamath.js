include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "w3a.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "wex.mm"
include "cwlkson.mm"
include "co.mm"
include "umgr2wlk.mm"
include "wa.mm"
include "simp1.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "com12.mm"
include "a1i.mm"
include "3imp.mm"
include "3jca.mm"
include "adantl.mm"
include "cvtx.mm"
include "cvv.mm"
include "wb.mm"
include "wne.mm"
include "umgr2adedgwlklem.mm"
include "simprr1.mm"
include "simprr3.mm"
include "jca.mm"
include "mpdan.mm"
include "vex.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "iswlkon.mm"
include "syl2an2r.mm"
include "mpbird.mm"
include "ex.mm"
include "2eximdv.mm"
include "mpd.mm"

theorem umgr2wlkon
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cE: class E
  let cG: class G
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  assume umgr2wlk.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint C f
  disjoint C p
  disjoint G f
  disjoint G p
  disjoint E f
  disjoint E p
  disjoint A i
  disjoint A j
  disjoint f i
  disjoint f j
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint E i
  disjoint E j
  disjoint G i
  disjoint G j
  assert |- ( ( G e. UMGraph /\ { A , B } e. E /\ { B , C } e. E ) -> E. f E. p f ( A ( WalksOn ` G ) C ) p )

  proof
    cG
    cumgr
    wcel
    cA
    cB
    cpr
    cE
    wcel
    cB
    cC
    cpr
    cE
    wcel
    w3a
    #
    vf
    cv
    #
    vp
    cv
    #
    cG
    cwlks
    cfv
    wbr
    #
    @1
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cc0
    @2
    cfv
    #
    wceq
    #
    cB
    c1
    @2
    cfv
    wceq
    #
    cC
    c2
    @2
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vp
    wex
    vf
    wex
    @1
    @2
    cA
    cC
    cG
    cwlkson
    cfv
    co
    wbr
    #
    vp
    wex
    vf
    wex
    cA
    cB
    cC
    vf
    cE
    cG
    vp
    umgr2wlk.e
    umgr2wlk
    @0
    @12
    @13
    vf
    vp
    @0
    @12
    @13
    @0
    @12
    wa
    #
    @13
    @3
    @6
    cA
    wceq
    #
    @4
    @2
    cfv
    #
    cC
    wceq
    #
    w3a
    #
    @12
    @18
    @0
    @12
    @3
    @15
    @17
    @3
    @5
    @11
    simp1
    @11
    @3
    @15
    @5
    @7
    @8
    @15
    @10
    @7
    @15
    cA
    @6
    eqcom
    biimpi
    3ad2ant1
    3ad2ant3
    @3
    @5
    @11
    @17
    @5
    @11
    @17
    wi
    wi
    @3
    @11
    @5
    @17
    @10
    @7
    @5
    @17
    wi
    #
    @8
    @19
    @9
    cC
    @5
    @9
    cC
    wceq
    @17
    @5
    @9
    @16
    cC
    @9
    @16
    wceq
    c2
    @4
    c2
    @4
    @2
    fveq2
    eqcoms
    eqeq1d
    biimpcd
    eqcoms
    3ad2ant3
    com12
    a1i
    3imp
    3jca
    adantl
    @0
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cC
    @20
    wcel
    #
    wa
    #
    @12
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    #
    @13
    @18
    wb
    @0
    cA
    cB
    wne
    cB
    cC
    wne
    wa
    #
    @21
    cB
    @20
    wcel
    #
    @22
    w3a
    wa
    #
    @23
    cA
    cB
    cC
    cE
    cG
    umgr2wlk.e
    umgr2adedgwlklem
    @0
    @29
    wa
    @21
    @22
    @21
    @28
    @22
    @27
    @0
    simprr1
    @21
    @28
    @22
    @27
    @0
    simprr3
    jca
    mpdan
    @26
    @14
    @24
    @25
    vf
    vex
    vp
    vex
    pm3.2i
    a1i
    cA
    cC
    @2
    cvv
    @1
    cG
    @20
    cvv
    @20
    eqid
    iswlkon
    syl2an2r
    mpbird
    ex
    2eximdv
    mpd
end
