include "wcel.mm"
include "cvv.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wceq.mm"
include "elex.mm"
include "wi.mm"
include "wal.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "wb.mm"
include "vex.mm"
include "elfi.mm"
include "mpan.mm"
include "biimpd.mm"
include "wex.mm"
include "df-rex.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "fiint.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "sstrd.mm"
include "eqvisset.mm"
include "intex.mm"
include "sylibr.mm"
include "3ad2ant3.mm"
include "inss2.mm"
include "3jca.mm"
include "3expib.mm"
include "pm2.27.mm"
include "syl6.mm"
include "eleq1.mm"
include "biimprd.mm"
include "adantl.mm"
include "a1i.mm"
include "syldd.mm"
include "com23.mm"
include "alimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "19.23v.mm"
include "sylib.mm"
include "sylan9.mm"
include "ssrdv.mm"
include "ex.mm"
include "alrimiv.mm"
include "ssintab.mm"
include "ssfii.mm"
include "fiin.mm"
include "rgen2a.mm"
include "fvex.mm"
include "sseq2.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "syl.mm"
include "eqssd.mm"

theorem dffi2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cV: class V
  let vt: setvar t
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint V y
  disjoint V z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A e. V -> ( fi ` A ) = |^| { z | ( A C_ z /\ A. x e. z A. y e. z ( x i^i y ) e. z ) } )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cA
    cfi
    cfv
    #
    cA
    vz
    cv
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    @2
    wcel
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    wa
    #
    vz
    cab
    #
    cint
    #
    wceq
    cA
    cV
    elex
    @0
    @1
    @12
    @0
    @10
    @1
    @2
    wss
    #
    wi
    #
    vz
    wal
    @1
    @12
    wss
    @0
    @14
    vz
    @0
    @10
    @13
    @0
    @10
    wa
    vt
    @1
    @2
    @0
    vt
    cv
    #
    @1
    wcel
    #
    @15
    @4
    cint
    #
    wceq
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @10
    @15
    @2
    wcel
    #
    @0
    @16
    @21
    @15
    cvv
    wcel
    @0
    @16
    @21
    wb
    vt
    vex
    vx
    @15
    cA
    cvv
    cvv
    elfi
    mpan
    biimpd
    @21
    @4
    @20
    wcel
    #
    @18
    wa
    #
    vx
    wex
    #
    @10
    @22
    @18
    vx
    @20
    df-rex
    @10
    @24
    @22
    wi
    #
    vx
    wal
    #
    @25
    @22
    wi
    @3
    @9
    @27
    @9
    @4
    @2
    wss
    #
    @4
    c0
    wne
    #
    @4
    cfn
    wcel
    #
    w3a
    #
    @17
    @2
    wcel
    #
    wi
    #
    vx
    wal
    @3
    @27
    vx
    vy
    @2
    fiint
    @3
    @33
    @26
    vx
    @3
    @24
    @33
    @22
    @3
    @24
    @33
    @32
    @22
    @3
    @24
    @31
    @33
    @32
    wi
    @3
    @23
    @18
    @31
    @3
    @23
    @18
    w3a
    #
    @28
    @29
    @30
    @34
    @4
    cA
    @2
    @23
    @3
    @4
    cA
    wss
    @18
    @23
    @4
    cA
    @20
    @19
    @4
    @19
    cfn
    inss1
    sseli
    elpwid
    3ad2ant2
    @3
    @23
    @18
    simp1
    sstrd
    @18
    @3
    @29
    @23
    @18
    @17
    cvv
    wcel
    @29
    vt
    @17
    eqvisset
    @4
    intex
    sylibr
    3ad2ant3
    @23
    @3
    @30
    @18
    @20
    cfn
    @4
    @19
    cfn
    inss2
    sseli
    3ad2ant2
    3jca
    3expib
    @31
    @32
    pm2.27
    syl6
    @24
    @32
    @22
    wi
    #
    wi
    @3
    @18
    @35
    @23
    @18
    @22
    @32
    @15
    @17
    @2
    eleq1
    biimprd
    adantl
    a1i
    syldd
    com23
    alimdv
    syl5bi
    imp
    @24
    @22
    vx
    19.23v
    sylib
    syl5bi
    sylan9
    ssrdv
    ex
    alrimiv
    @10
    vz
    @1
    ssintab
    sylibr
    @0
    @1
    @11
    wcel
    #
    @12
    @1
    wss
    @0
    cA
    @1
    wss
    #
    @6
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @36
    cA
    cvv
    ssfii
    @40
    @0
    @38
    vx
    vy
    @1
    @4
    @5
    cA
    fiin
    rgen2a
    a1i
    @10
    @37
    @40
    wa
    vz
    @1
    cA
    cfi
    fvex
    @2
    @1
    wceq
    @3
    @37
    @9
    @40
    @2
    @1
    cA
    sseq2
    @8
    @39
    vx
    @2
    @1
    @7
    @38
    vy
    @2
    @1
    @2
    @1
    @6
    eleq2
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elab
    sylanbrc
    @1
    @11
    intss1
    syl
    eqssd
    syl
end
