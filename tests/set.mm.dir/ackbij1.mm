include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wf1o.mm"
include "wf1.mm"
include "crn.mm"
include "wceq.mm"
include "ackbij1lem17.mm"
include "wf.mm"
include "wss.mm"
include "f1f.mm"
include "frn.mm"
include "mp2b.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "csuc.mm"
include "eleq1.mm"
include "cfv.mm"
include "wrex.mm"
include "peano1.mm"
include "ackbij1lem3.mm"
include "ax-mp.mm"
include "ackbij1lem13.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "wfn.mm"
include "wb.mm"
include "f1fn.mm"
include "fvelrnb.mm"
include "mpbir.mm"
include "wa.mm"
include "ackbij1lem18.mm"
include "adantl.mm"
include "suceq.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "3imtr4g.mm"
include "finds.mm"
include "ssriv.mm"
include "eqssi.mm"
include "dff1o5.mm"
include "mpbir2an.mm"

theorem ackbij1
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cA: class A
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- F : ( ~P _om i^i Fin ) -1-1-onto-> _om

  proof
    com
    cpw
    cfn
    cin
    #
    com
    cF
    wf1o
    @0
    com
    cF
    wf1
    #
    cF
    crn
    #
    com
    wceq
    vx
    vy
    cF
    ackbij.f
    ackbij1lem17
    #
    @2
    com
    @1
    @0
    com
    cF
    wf
    @2
    com
    wss
    @3
    @0
    com
    cF
    f1f
    @0
    com
    cF
    frn
    mp2b
    va
    com
    @2
    vb
    cv
    #
    @2
    wcel
    c0
    @2
    wcel
    #
    va
    cv
    #
    @2
    wcel
    #
    @6
    csuc
    #
    @2
    wcel
    #
    @7
    vb
    va
    @6
    @4
    c0
    @2
    eleq1
    @4
    @6
    @2
    eleq1
    #
    @4
    @8
    @2
    eleq1
    @10
    @5
    @6
    cF
    cfv
    #
    c0
    wceq
    #
    va
    @0
    wrex
    #
    c0
    @0
    wcel
    #
    c0
    cF
    cfv
    #
    c0
    wceq
    #
    @13
    c0
    com
    wcel
    @14
    peano1
    c0
    ackbij1lem3
    ax-mp
    vx
    vy
    cF
    ackbij.f
    ackbij1lem13
    @12
    @16
    va
    c0
    @0
    @6
    c0
    wceq
    @11
    @15
    c0
    @6
    c0
    cF
    fveq2
    eqeq1d
    rspcev
    mp2an
    cF
    @0
    wfn
    #
    @5
    @13
    wb
    @1
    @17
    @3
    @0
    com
    cF
    f1fn
    ax-mp
    #
    va
    @0
    c0
    cF
    fvelrnb
    ax-mp
    mpbir
    @6
    com
    wcel
    #
    vc
    cv
    #
    cF
    cfv
    #
    @6
    wceq
    #
    vc
    @0
    wrex
    #
    @4
    cF
    cfv
    #
    @8
    wceq
    #
    vb
    @0
    wrex
    #
    @7
    @9
    @19
    @22
    @26
    vc
    @0
    @19
    @20
    @0
    wcel
    #
    wa
    @24
    @21
    csuc
    #
    wceq
    #
    vb
    @0
    wrex
    #
    @22
    @26
    @27
    @30
    @19
    vx
    vy
    @20
    cF
    vb
    ackbij.f
    ackbij1lem18
    adantl
    @22
    @29
    @25
    vb
    @0
    @22
    @28
    @8
    @24
    @21
    @6
    suceq
    eqeq2d
    rexbidv
    syl5ibcom
    rexlimdva
    @17
    @7
    @23
    wb
    @18
    vc
    @0
    @6
    cF
    fvelrnb
    ax-mp
    @17
    @9
    @26
    wb
    @18
    vb
    @0
    @8
    cF
    fvelrnb
    ax-mp
    3imtr4g
    finds
    ssriv
    eqssi
    @0
    com
    cF
    dff1o5
    mpbir2an
end
