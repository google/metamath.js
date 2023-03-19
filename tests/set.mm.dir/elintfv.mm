include "cima.mm"
include "cint.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wral.mm"
include "elint.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "wb.mm"
include "ssel2.mm"
include "fnbrfvb.mm"
include "sylan2.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "vex.mm"
include "elima.mm"
include "syl6rbbr.mm"
include "imbi1d.mm"
include "r19.23v.mm"
include "syl6bbr.mm"
include "albidv.mm"
include "ralcom4.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "albii.mm"
include "fvex.mm"
include "eleq2.mm"
include "ceqsalv.mm"
include "bitri.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "syl5bb.mm"

theorem elintfv
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vz: setvar z
  assume elintfv.1: |- X e. _V

  disjoint A y
  disjoint B y
  disjoint F y
  disjoint X y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint F z
  disjoint X z
  assert |- ( ( F Fn A /\ B C_ A ) -> ( X e. |^| ( F " B ) <-> A. y e. B X e. ( F ` y ) ) )

  proof
    cX
    cF
    cB
    cima
    #
    cint
    wcel
    vz
    cv
    #
    @0
    wcel
    #
    cX
    @1
    wcel
    #
    wi
    #
    vz
    wal
    #
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    wa
    #
    cX
    vy
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vy
    cB
    wral
    #
    vz
    cX
    @0
    elintfv.1
    elint
    @8
    @5
    @10
    @1
    wceq
    #
    @3
    wi
    #
    vy
    cB
    wral
    #
    vz
    wal
    #
    @12
    @8
    @4
    @15
    vz
    @8
    @4
    @13
    vy
    cB
    wrex
    #
    @3
    wi
    @15
    @8
    @2
    @17
    @3
    @8
    @17
    @9
    @1
    cF
    wbr
    #
    vy
    cB
    wrex
    @2
    @8
    @13
    @18
    vy
    cB
    @6
    @7
    @9
    cB
    wcel
    #
    @13
    @18
    wb
    #
    @7
    @19
    wa
    @6
    @9
    cA
    wcel
    @20
    cB
    cA
    @9
    ssel2
    cA
    @9
    @1
    cF
    fnbrfvb
    sylan2
    anassrs
    rexbidva
    vy
    @1
    cF
    cB
    vz
    vex
    elima
    syl6rbbr
    imbi1d
    @13
    @3
    vy
    cB
    r19.23v
    syl6bbr
    albidv
    @16
    @14
    vz
    wal
    #
    vy
    cB
    wral
    @12
    @14
    vy
    vz
    cB
    ralcom4
    @21
    @11
    vy
    cB
    @21
    @1
    @10
    wceq
    #
    @3
    wi
    #
    vz
    wal
    @11
    @14
    @23
    vz
    @13
    @22
    @3
    @10
    @1
    eqcom
    imbi1i
    albii
    @3
    @11
    vz
    @10
    @9
    cF
    fvex
    @1
    @10
    cX
    eleq2
    ceqsalv
    bitri
    ralbii
    bitr3i
    syl6bb
    syl5bb
end
