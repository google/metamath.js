include "csh.mm"
include "wcel.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "an4.mm"
include "reeanv.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simplrl.mm"
include "simprll.mm"
include "simplrr.mm"
include "simprlr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "eqtr3d.mm"
include "shuni.mm"
include "simpld.mm"
include "exp32.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "expimpd.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "mo4.mm"
include "sylibr.mm"

theorem pjhthmo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  assert |- ( ( A e. SH /\ B e. SH /\ ( A i^i B ) = 0H ) -> E* x ( x e. A /\ E. y e. B C = ( x +h y ) ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cA
    cB
    cin
    c0h
    wceq
    #
    w3a
    #
    vx
    cv
    #
    cA
    wcel
    #
    cC
    @4
    vy
    cv
    #
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    #
    cC
    @11
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vw
    cB
    wrex
    #
    wa
    #
    wa
    #
    @4
    @11
    wceq
    #
    wi
    #
    vz
    wal
    vx
    wal
    @10
    vx
    wmo
    @3
    @20
    vx
    vz
    @18
    @5
    @12
    wa
    #
    @9
    @16
    wa
    #
    wa
    @3
    @19
    @5
    @12
    @9
    @16
    an4
    @3
    @21
    @22
    @19
    @22
    @8
    @15
    wa
    #
    vw
    cB
    wrex
    vy
    cB
    wrex
    @3
    @21
    wa
    #
    @19
    @8
    @15
    vy
    vw
    cB
    cB
    reeanv
    @24
    @23
    @19
    vy
    vw
    cB
    cB
    @24
    @6
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    wa
    #
    @23
    @19
    @24
    @27
    @23
    wa
    #
    wa
    #
    @19
    @6
    @13
    wceq
    #
    @29
    @4
    @6
    @11
    @13
    cA
    cB
    @0
    @1
    @2
    @21
    @28
    simpll1
    @0
    @1
    @2
    @21
    @28
    simpll2
    @0
    @1
    @2
    @21
    @28
    simpll3
    @3
    @5
    @12
    @28
    simplrl
    @24
    @25
    @26
    @23
    simprll
    @3
    @5
    @12
    @28
    simplrr
    @24
    @25
    @26
    @23
    simprlr
    @29
    cC
    @7
    @14
    @24
    @27
    @8
    @15
    simprrl
    @24
    @27
    @8
    @15
    simprrr
    eqtr3d
    shuni
    simpld
    exp32
    rexlimdvv
    syl5bir
    expimpd
    syl5bir
    alrimivv
    @10
    @17
    vx
    vz
    @19
    @5
    @12
    @9
    @16
    @4
    @11
    cA
    eleq1
    @19
    @9
    cC
    @11
    @6
    cva
    co
    #
    wceq
    #
    vy
    cB
    wrex
    @16
    @19
    @8
    @32
    vy
    cB
    @19
    @7
    @31
    cC
    @4
    @11
    @6
    cva
    oveq1
    eqeq2d
    rexbidv
    @32
    @15
    vy
    vw
    cB
    @30
    @31
    @14
    cC
    @6
    @13
    @11
    cva
    oveq2
    eqeq2d
    cbvrexv
    syl6bb
    anbi12d
    mo4
    sylibr
end
