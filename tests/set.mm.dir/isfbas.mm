include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "cvv.mm"
include "cfbas.mm"
include "cfv.mm"
include "wb.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "elex.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "df-fbas.mm"
include "wceq.mm"
include "neeq1.mm"
include "neleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "raleqbi1dv.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "pweq.mm"
include "pweqd.mm"
include "vpwex.mm"
include "pwex.mm"
include "a1i.mm"
include "elmptrab.mm"
include "3anass.mm"
include "bitri.mm"
include "syl6rbbr.mm"

theorem isfbas
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint F z
  disjoint F w
  disjoint B z
  disjoint B w
  assert |- ( B e. A -> ( F e. ( fBas ` B ) <-> ( F C_ ~P B /\ ( F =/= (/) /\ (/) e/ F /\ A. x e. F A. y e. F ( F i^i ~P ( x i^i y ) ) =/= (/) ) ) ) )

  proof
    cB
    cA
    wcel
    #
    cF
    cB
    cpw
    #
    wss
    #
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    cF
    vx
    cv
    vy
    cv
    cin
    cpw
    #
    cin
    #
    c0
    wne
    #
    vy
    cF
    wral
    #
    vx
    cF
    wral
    #
    w3a
    #
    wa
    #
    cB
    cvv
    wcel
    #
    cF
    @1
    cpw
    #
    wcel
    #
    @10
    wa
    #
    wa
    #
    cF
    cB
    cfbas
    cfv
    wcel
    #
    @0
    @15
    @11
    @16
    @0
    @14
    @2
    @10
    @0
    @1
    cvv
    wcel
    @14
    @2
    wb
    cB
    cA
    pwexg
    cF
    @1
    cvv
    elpw2g
    syl
    anbi1d
    @0
    @12
    @15
    cB
    cA
    elex
    biantrurd
    bitr3d
    @17
    @12
    @14
    @10
    w3a
    @16
    vw
    cv
    #
    c0
    wne
    #
    c0
    @18
    wnel
    #
    @18
    @5
    cin
    #
    c0
    wne
    #
    vy
    @18
    wral
    #
    vx
    @18
    wral
    #
    w3a
    #
    @10
    vz
    vw
    vz
    cv
    #
    cpw
    #
    cpw
    #
    @13
    cvv
    cfbas
    cvv
    cB
    cF
    vw
    vx
    vy
    vz
    df-fbas
    @18
    cF
    wceq
    #
    @25
    @10
    wb
    @26
    cB
    wceq
    #
    @29
    @19
    @3
    @20
    @4
    @24
    @9
    @18
    cF
    c0
    neeq1
    @18
    cF
    c0
    neleq2
    @23
    @8
    vx
    @18
    cF
    @22
    @7
    vy
    @18
    cF
    @29
    @21
    @6
    c0
    @18
    cF
    @5
    ineq1
    neeq1d
    raleqbi1dv
    raleqbi1dv
    3anbi123d
    adantl
    @30
    @27
    @1
    @26
    cB
    pweq
    pweqd
    @28
    cvv
    wcel
    @26
    cvv
    wcel
    @27
    vz
    vpwex
    pwex
    a1i
    elmptrab
    @12
    @14
    @10
    3anass
    bitri
    syl6rbbr
end
