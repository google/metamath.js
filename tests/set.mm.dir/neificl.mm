include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "simprl.mm"
include "cv.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "innei.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "fiint.mm"
include "sylib.mm"
include "wceq.mm"
include "sseq1.mm"
include "neeq1.mm"
include "eleq1.mm"
include "3anbi123d.mm"
include "3ancomb.mm"
include "3anass.mm"
include "bitri.mm"
include "syl6bb.mm"
include "inteq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl5.mm"
include "com3l.mm"
include "mpdi.mm"
include "impl.mm"

theorem neificl
  let cS: class S
  let cJ: class J
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( J e. Top /\ N C_ ( ( nei ` J ) ` S ) ) /\ ( N e. Fin /\ N =/= (/) ) ) -> |^| N e. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    #
    wss
    #
    cN
    cfn
    wcel
    #
    cN
    c0
    wne
    #
    wa
    #
    cN
    cint
    #
    @1
    wcel
    #
    @0
    @2
    @5
    wa
    #
    @3
    @7
    @2
    @3
    @4
    simprl
    @3
    @0
    @8
    @7
    @0
    vx
    cv
    #
    @1
    wss
    #
    @9
    c0
    wne
    #
    @9
    cfn
    wcel
    #
    w3a
    #
    @9
    cint
    #
    @1
    wcel
    #
    wi
    #
    vx
    wal
    #
    @3
    @8
    @7
    wi
    #
    @0
    @9
    vy
    cv
    #
    cin
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @17
    @0
    @20
    vx
    vy
    @1
    @1
    @0
    @9
    @1
    wcel
    @19
    @1
    wcel
    @20
    cS
    cJ
    @19
    @9
    innei
    3expib
    ralrimivv
    vx
    vy
    @1
    fiint
    sylib
    @16
    @18
    vx
    cN
    cfn
    @9
    cN
    wceq
    #
    @13
    @8
    @15
    @7
    @21
    @13
    @2
    @4
    @3
    w3a
    #
    @8
    @21
    @10
    @2
    @11
    @4
    @12
    @3
    @9
    cN
    @1
    sseq1
    @9
    cN
    c0
    neeq1
    @9
    cN
    cfn
    eleq1
    3anbi123d
    @22
    @2
    @3
    @4
    w3a
    @8
    @2
    @4
    @3
    3ancomb
    @2
    @3
    @4
    3anass
    bitri
    syl6bb
    @21
    @14
    @6
    @1
    @9
    cN
    inteq
    eleq1d
    imbi12d
    spcgv
    syl5
    com3l
    mpdi
    impl
end
