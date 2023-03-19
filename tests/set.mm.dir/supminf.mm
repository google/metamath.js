include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "negn0.mm"
include "ublbneg.mm"
include "ssrab2.mm"
include "infrenegsup.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "3impa.mm"
include "elrabi.mm"
include "adantl.mm"
include "ssel2.mm"
include "wb.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "renegcl.mm"
include "syl.mm"
include "recn.mm"
include "negnegd.mm"
include "3bitrd.mm"
include "eqrdav.mm"
include "supeq1d.mm"
include "3ad2ant1.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "infrecl.mm"
include "suprcl.mm"
include "cc.mm"
include "negcon2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem supminf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) -> sup ( A , RR , < ) = -u inf ( { z e. RR | -u z e. A } , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    vz
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vz
    cr
    crab
    #
    cr
    clt
    cinf
    #
    cA
    cr
    clt
    csup
    #
    cneg
    #
    wceq
    #
    @11
    @10
    cneg
    wceq
    #
    @5
    @10
    vw
    cv
    #
    cneg
    #
    @9
    wcel
    #
    vw
    cr
    crab
    #
    cr
    clt
    csup
    #
    cneg
    #
    @12
    @0
    @1
    @4
    @10
    @20
    wceq
    #
    @0
    @1
    wa
    #
    @9
    c0
    wne
    #
    @3
    @2
    cle
    wbr
    vy
    @9
    wral
    vx
    cr
    wrex
    #
    @21
    @4
    vz
    cA
    negn0
    #
    vx
    vy
    vz
    cA
    ublbneg
    #
    @9
    cr
    wss
    #
    @23
    @24
    @21
    @8
    vz
    cr
    ssrab2
    #
    vx
    vy
    vw
    @9
    infrenegsup
    mp3an1
    syl2an
    3impa
    @5
    @19
    @11
    @0
    @1
    @19
    @11
    wceq
    @4
    @0
    cr
    @18
    cA
    clt
    @0
    vx
    @18
    cA
    cr
    @3
    @18
    wcel
    #
    @3
    cr
    wcel
    #
    @0
    @17
    vw
    @3
    cr
    elrabi
    adantl
    cA
    cr
    @3
    ssel2
    @30
    @29
    @3
    cA
    wcel
    #
    wb
    @0
    @30
    @29
    @3
    cneg
    #
    @9
    wcel
    #
    @32
    cneg
    #
    cA
    wcel
    #
    @31
    @17
    @33
    vw
    @3
    cr
    @15
    @3
    wceq
    @16
    @32
    @9
    @15
    @3
    negeq
    eleq1d
    elrab3
    @30
    @32
    cr
    wcel
    @33
    @35
    wb
    @3
    renegcl
    @8
    @35
    vz
    @32
    cr
    @6
    @32
    wceq
    @7
    @34
    cA
    @6
    @32
    negeq
    eleq1d
    elrab3
    syl
    @30
    @34
    @3
    cA
    @30
    @3
    @3
    recn
    negnegd
    eleq1d
    3bitrd
    adantl
    eqrdav
    supeq1d
    3ad2ant1
    negeqd
    eqtrd
    @5
    @10
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @13
    @14
    wb
    #
    @0
    @1
    @4
    @36
    @22
    @23
    @24
    @36
    @4
    @25
    @26
    @27
    @23
    @24
    @36
    @28
    vx
    vy
    @9
    infrecl
    mp3an1
    syl2an
    3impa
    vx
    vy
    cA
    suprcl
    @36
    @10
    cc
    wcel
    @11
    cc
    wcel
    @38
    @37
    @10
    recn
    @11
    recn
    @10
    @11
    negcon2
    syl2an
    syl2anc
    mpbid
end
