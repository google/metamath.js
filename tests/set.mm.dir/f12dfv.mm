include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "dff14b.mm"
include "cpr.mm"
include "raleqi.mm"
include "wb.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "raleqbidv.mm"
include "ralprg.mm"
include "adantr.mm"
include "difeq1i.mm"
include "difprsn1.mm"
include "syl5eq.mm"
include "adantl.mm"
include "raleqdv.mm"
include "neeq2d.mm"
include "ralsng.mm"
include "bitrd.mm"
include "difprsn2.mm"
include "anbi12d.mm"
include "necom.mm"
include "biimpi.mm"
include "pm4.71i.mm"
include "syl6bbr.mm"
include "syl5bb.mm"
include "anbi2d.mm"

theorem f12dfv
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume f12dfv.a: |- A = { X , Y }


  assert |- ( ( ( X e. U /\ Y e. V ) /\ X =/= Y ) -> ( F : A -1-1-> B <-> ( F : A --> B /\ ( F ` X ) =/= ( F ` Y ) ) ) )

  proof
    cA
    cB
    cF
    wf1
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wne
    #
    vy
    cA
    @1
    csn
    #
    cdif
    #
    wral
    #
    vx
    cA
    wral
    #
    wa
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    cX
    cY
    wne
    #
    wa
    #
    @0
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    wne
    #
    wa
    vx
    vy
    cA
    cB
    cF
    dff14b
    @14
    @9
    @17
    @0
    @9
    @8
    vx
    cX
    cY
    cpr
    #
    wral
    #
    @14
    @17
    @8
    vx
    cA
    @18
    f12dfv.a
    raleqi
    @14
    @19
    @15
    @4
    wne
    #
    vy
    cA
    cX
    csn
    #
    cdif
    #
    wral
    #
    @16
    @4
    wne
    #
    vy
    cA
    cY
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    @17
    @12
    @19
    @28
    wb
    @13
    @8
    @23
    @27
    vx
    cX
    cY
    cU
    cV
    @1
    cX
    wceq
    #
    @5
    @20
    vy
    @7
    @22
    @29
    @6
    @21
    cA
    @1
    cX
    sneq
    difeq2d
    @29
    @2
    @15
    @4
    @1
    cX
    cF
    fveq2
    neeq1d
    raleqbidv
    @1
    cY
    wceq
    #
    @5
    @24
    vy
    @7
    @26
    @30
    @6
    @25
    cA
    @1
    cY
    sneq
    difeq2d
    @30
    @2
    @16
    @4
    @1
    cY
    cF
    fveq2
    neeq1d
    raleqbidv
    ralprg
    adantr
    @14
    @28
    @17
    @16
    @15
    wne
    #
    wa
    @17
    @14
    @23
    @17
    @27
    @31
    @14
    @23
    @20
    vy
    @25
    wral
    #
    @17
    @14
    @20
    vy
    @22
    @25
    @13
    @22
    @25
    wceq
    @12
    @13
    @22
    @18
    @21
    cdif
    @25
    cA
    @18
    @21
    f12dfv.a
    difeq1i
    cX
    cY
    difprsn1
    syl5eq
    adantl
    raleqdv
    @12
    @32
    @17
    wb
    #
    @13
    @11
    @33
    @10
    @20
    @17
    vy
    cY
    cV
    @3
    cY
    wceq
    @4
    @16
    @15
    @3
    cY
    cF
    fveq2
    neeq2d
    ralsng
    adantl
    adantr
    bitrd
    @14
    @27
    @24
    vy
    @21
    wral
    #
    @31
    @14
    @24
    vy
    @26
    @21
    @13
    @26
    @21
    wceq
    @12
    @13
    @26
    @18
    @25
    cdif
    @21
    cA
    @18
    @25
    f12dfv.a
    difeq1i
    cX
    cY
    difprsn2
    syl5eq
    adantl
    raleqdv
    @12
    @34
    @31
    wb
    #
    @13
    @10
    @35
    @11
    @24
    @31
    vy
    cX
    cU
    @3
    cX
    wceq
    @4
    @15
    @16
    @3
    cX
    cF
    fveq2
    neeq2d
    ralsng
    adantr
    adantr
    bitrd
    anbi12d
    @17
    @31
    @17
    @31
    @15
    @16
    necom
    biimpi
    pm4.71i
    syl6bbr
    bitrd
    syl5bb
    anbi2d
    syl5bb
end
