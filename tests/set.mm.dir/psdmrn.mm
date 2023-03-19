include "cps.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "cun.mm"
include "ssun1.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "pslem.mm"
include "simp2d.mm"
include "vex.mm"
include "breldm.mm"
include "syl6.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ssun2.mm"
include "brelrn.mm"
include "jca.mm"

theorem psdmrn
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( R e. PosetRel -> ( dom R = U. U. R /\ ran R = U. U. R ) )

  proof
    cR
    cps
    wcel
    #
    cR
    cdm
    #
    cR
    cuni
    cuni
    #
    wceq
    cR
    crn
    #
    @2
    wceq
    @0
    @1
    @2
    @1
    @2
    wss
    @0
    @1
    @1
    @3
    cun
    #
    @2
    @1
    @3
    ssun1
    cR
    dmrnssfld
    #
    sstri
    a1i
    @0
    vx
    @2
    @1
    @0
    vx
    cv
    #
    @2
    wcel
    #
    @6
    @6
    cR
    wbr
    #
    @6
    @1
    wcel
    @0
    @8
    @8
    wa
    #
    @8
    wi
    @7
    @8
    wi
    @9
    @6
    @6
    wceq
    wi
    @6
    @6
    @6
    cR
    pslem
    simp2d
    #
    @6
    @6
    cR
    vx
    vex
    #
    @11
    breldm
    syl6
    ssrdv
    eqssd
    @0
    @3
    @2
    @3
    @2
    wss
    @0
    @3
    @4
    @2
    @3
    @1
    ssun2
    @5
    sstri
    a1i
    @0
    vx
    @2
    @3
    @0
    @7
    @8
    @6
    @3
    wcel
    @10
    @6
    @6
    cR
    @11
    @11
    brelrn
    syl6
    ssrdv
    eqssd
    jca
end
