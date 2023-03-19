include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "crio.mm"
include "wb.mm"
include "flval.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "wreu.mm"
include "rebtwnz.mm"
include "breq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "sylan2.mm"
include "ancoms.mm"
include "bitr4d.mm"

theorem flbi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. ZZ ) -> ( ( |_ ` A ) = B <-> ( B <_ A /\ A < ( B + 1 ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cA
    cfl
    cfv
    #
    cB
    wceq
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    cA
    @4
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    #
    cB
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    cA
    cB
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @0
    @3
    @10
    wb
    @1
    @0
    @2
    @9
    cB
    vx
    cA
    flval
    eqeq1d
    adantr
    @1
    @0
    @14
    @10
    wb
    #
    @0
    @1
    @8
    vx
    cz
    wreu
    @15
    vx
    cA
    rebtwnz
    @8
    @14
    vx
    cz
    cB
    @4
    cB
    wceq
    #
    @5
    @11
    @7
    @13
    @4
    cB
    cA
    cle
    breq1
    @16
    @6
    @12
    cA
    clt
    @4
    cB
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    sylan2
    ancoms
    bitr4d
end
