include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cv.mm"
include "cz.mm"
include "crio.mm"
include "wceq.mm"
include "flval.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "flcl.mm"
include "rebtwnz.mm"
include "breq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem fllelt
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. RR -> ( ( |_ ` A ) <_ A /\ A < ( ( |_ ` A ) + 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    #
    cA
    cle
    wbr
    #
    cA
    @1
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
    cv
    #
    cA
    cle
    wbr
    #
    cA
    @6
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
    @1
    wceq
    #
    @0
    @1
    @11
    vx
    cA
    flval
    eqcomd
    @0
    @1
    cz
    wcel
    @10
    vx
    cz
    wreu
    @5
    @12
    wb
    cA
    flcl
    vx
    cA
    rebtwnz
    @10
    @5
    vx
    cz
    @1
    @6
    @1
    wceq
    #
    @7
    @2
    @9
    @4
    @6
    @1
    cA
    cle
    breq1
    @13
    @8
    @3
    cA
    clt
    @6
    @1
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    syl2anc
    mpbird
end
