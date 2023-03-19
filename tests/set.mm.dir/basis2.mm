include "ctb.mm"
include "wcel.mm"
include "cin.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "isbasis2g.mm"
include "ibi.mm"
include "wceq.mm"
include "wb.mm"
include "ineq1.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "ineq2.mm"
include "rspc2v.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rspccv.mm"
include "syl6com.mm"
include "expd.mm"
include "imp43.mm"

theorem basis2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint w x
  disjoint A w
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( ( ( B e. TopBases /\ C e. B ) /\ ( D e. B /\ A e. ( C i^i D ) ) ) -> E. x e. B ( A e. x /\ x C_ ( C i^i D ) ) )

  proof
    cB
    ctb
    wcel
    #
    cC
    cB
    wcel
    #
    cD
    cB
    wcel
    #
    cA
    cC
    cD
    cin
    #
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    @5
    @3
    wss
    #
    wa
    #
    vx
    cB
    wrex
    #
    @0
    @1
    @2
    @4
    @9
    wi
    #
    @0
    vw
    cv
    #
    @5
    wcel
    #
    @5
    vy
    cv
    #
    vz
    cv
    #
    cin
    #
    wss
    #
    wa
    #
    vx
    cB
    wrex
    #
    vw
    @15
    wral
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    @1
    @2
    wa
    #
    @10
    wi
    @0
    @20
    vy
    vz
    vw
    vx
    cB
    ctb
    isbasis2g
    ibi
    @21
    @20
    @12
    @7
    wa
    #
    vx
    cB
    wrex
    #
    vw
    @3
    wral
    #
    @10
    @19
    @24
    @12
    @5
    cC
    @14
    cin
    #
    wss
    #
    wa
    #
    vx
    cB
    wrex
    #
    vw
    @25
    wral
    #
    vy
    vz
    cC
    cD
    cB
    cB
    @13
    cC
    wceq
    @15
    @25
    wceq
    #
    @19
    @29
    wb
    @13
    cC
    @14
    ineq1
    @18
    @28
    vw
    @15
    @25
    @30
    @17
    @27
    vx
    cB
    @30
    @16
    @26
    @12
    @15
    @25
    @5
    sseq2
    anbi2d
    rexbidv
    raleqbi1dv
    syl
    @14
    cD
    wceq
    @25
    @3
    wceq
    #
    @29
    @24
    wb
    @14
    cD
    cC
    ineq2
    @28
    @23
    vw
    @25
    @3
    @31
    @27
    @22
    vx
    cB
    @31
    @26
    @7
    @12
    @25
    @3
    @5
    sseq2
    anbi2d
    rexbidv
    raleqbi1dv
    syl
    rspc2v
    @23
    @9
    vw
    cA
    @3
    @11
    cA
    wceq
    #
    @22
    @8
    vx
    cB
    @32
    @12
    @6
    @7
    @11
    cA
    @5
    eleq1
    anbi1d
    rexbidv
    rspccv
    syl6com
    syl
    expd
    imp43
end
