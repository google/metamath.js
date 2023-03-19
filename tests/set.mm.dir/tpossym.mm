include "cxp.mm"
include "wfn.mm"
include "ctpos.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wb.mm"
include "tposfn.mm"
include "eqfnov2.mm"
include "mpancom.mm"
include "eqcom.mm"
include "ovtpos.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "2ralbii.mm"
include "syl6bb.mm"

theorem tpossym
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G x
  assert |- ( F Fn ( A X. A ) -> ( tpos F = F <-> A. x e. A A. y e. A ( x F y ) = ( y F x ) ) )

  proof
    cF
    cA
    cA
    cxp
    #
    wfn
    #
    cF
    ctpos
    #
    cF
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    @4
    @5
    cF
    co
    #
    wceq
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @7
    @5
    @4
    cF
    co
    #
    wceq
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @2
    @0
    wfn
    @1
    @3
    @9
    wb
    cA
    cA
    cF
    tposfn
    vx
    vy
    cA
    cA
    @2
    cF
    eqfnov2
    mpancom
    @8
    @11
    vx
    vy
    cA
    cA
    @8
    @7
    @6
    wceq
    @11
    @6
    @7
    eqcom
    @6
    @10
    @7
    @4
    @5
    cF
    ovtpos
    eqeq2i
    bitri
    2ralbii
    syl6bb
end
