include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "wal.mm"
include "cvv.mm"
include "c0.mm"
include "wpss.mm"
include "cnq.mm"
include "w3a.mm"
include "wral.mm"
include "elnpi.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "simprd.mm"
include "vtoclg.mm"
include "anabsi7.mm"

theorem prnmax
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. P. /\ B e. A ) -> E. x e. A B <Q x )

  proof
    cA
    cnp
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    vx
    cv
    #
    cltq
    wbr
    #
    vx
    cA
    wrex
    #
    @0
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    @5
    @2
    cltq
    wbr
    #
    vx
    cA
    wrex
    #
    wi
    @0
    @1
    wa
    #
    @4
    wi
    vy
    cB
    cA
    @5
    cB
    wceq
    #
    @7
    @10
    @9
    @4
    @11
    @6
    @1
    @0
    @5
    cB
    cA
    eleq1
    anbi2d
    @11
    @8
    @3
    vx
    cA
    @5
    cB
    @2
    cltq
    breq1
    rexbidv
    imbi12d
    @7
    @2
    @5
    cltq
    wbr
    @2
    cA
    wcel
    wi
    vx
    wal
    #
    @9
    @0
    @12
    @9
    wa
    #
    vy
    cA
    @0
    cA
    cvv
    wcel
    c0
    cA
    wpss
    cA
    cnq
    wpss
    w3a
    @13
    vy
    cA
    wral
    vy
    vx
    cA
    elnpi
    simprbi
    r19.21bi
    simprd
    vtoclg
    anabsi7
end
