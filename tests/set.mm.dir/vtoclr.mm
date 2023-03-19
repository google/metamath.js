include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "jca.mm"
include "cv.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "vtoclg.mm"
include "vtocl2g.mm"
include "syl2im.mm"
include "imp.mm"
include "pm2.43i.mm"

theorem vtoclr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume vtoclr.1: |- Rel R
  assume vtoclr.2: |- ( ( x R y /\ y R z ) -> x R z )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( A R B /\ B R C ) -> A R C )

  proof
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    cA
    cC
    cR
    wbr
    #
    @0
    @1
    @2
    @3
    wi
    #
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    @1
    cC
    cvv
    wcel
    #
    @4
    @0
    @5
    @6
    cA
    cB
    cR
    vtoclr.1
    brrelexi
    cA
    cB
    cR
    vtoclr.1
    brrelex2i
    jca
    cB
    cC
    cR
    vtoclr.1
    brrelex2i
    @7
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @9
    cC
    cR
    wbr
    #
    wa
    #
    @8
    cC
    cR
    wbr
    #
    wi
    #
    wi
    @7
    cA
    @9
    cR
    wbr
    #
    @11
    wa
    #
    @3
    wi
    #
    wi
    @7
    @4
    wi
    vx
    vy
    cA
    cB
    cvv
    cvv
    @8
    cA
    wceq
    #
    @14
    @17
    @7
    @18
    @12
    @16
    @13
    @3
    @18
    @10
    @15
    @11
    @8
    cA
    @9
    cR
    breq1
    anbi1d
    @8
    cA
    cC
    cR
    breq1
    imbi12d
    imbi2d
    @9
    cB
    wceq
    #
    @17
    @4
    @7
    @19
    @16
    @2
    @3
    @19
    @15
    @0
    @11
    @1
    @9
    cB
    cA
    cR
    breq2
    @9
    cB
    cC
    cR
    breq1
    anbi12d
    imbi1d
    imbi2d
    @10
    @9
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @8
    @20
    cR
    wbr
    #
    wi
    @14
    vz
    cC
    cvv
    @20
    cC
    wceq
    #
    @22
    @12
    @23
    @13
    @24
    @21
    @11
    @10
    @20
    cC
    @9
    cR
    breq2
    anbi2d
    @20
    cC
    @8
    cR
    breq2
    imbi12d
    vtoclr.2
    vtoclg
    vtocl2g
    syl2im
    imp
    pm2.43i
end
