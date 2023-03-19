include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "ciin.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wn.mm"
include "wa.mm"
include "r19.28zv.mm"
include "eldif.mm"
include "bicomi.mm"
include "ralbii.mm"
include "wrex.mm"
include "ralnex.mm"
include "eliun.mm"
include "xchbinxr.mm"
include "anbi2i.mm"
include "3bitr3g.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem iindif2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A =/= (/) -> |^|_ x e. A ( B \ C ) = ( B \ U_ x e. A C ) )

  proof
    cA
    c0
    wne
    #
    vy
    vx
    cA
    cB
    cC
    cdif
    #
    ciin
    #
    cB
    vx
    cA
    cC
    ciun
    #
    cdif
    #
    @0
    vy
    cv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    @5
    cB
    wcel
    #
    @5
    @3
    wcel
    #
    wn
    #
    wa
    #
    @5
    @2
    wcel
    #
    @5
    @4
    wcel
    @0
    @8
    @5
    cC
    wcel
    #
    wn
    #
    wa
    #
    vx
    cA
    wral
    @8
    @14
    vx
    cA
    wral
    #
    wa
    @7
    @11
    @8
    @14
    vx
    cA
    r19.28zv
    @15
    @6
    vx
    cA
    @6
    @15
    @5
    cB
    cC
    eldif
    bicomi
    ralbii
    @16
    @10
    @8
    @16
    @13
    vx
    cA
    wrex
    @9
    @13
    vx
    cA
    ralnex
    vx
    @5
    cA
    cC
    eliun
    xchbinxr
    anbi2i
    3bitr3g
    @5
    cvv
    wcel
    @12
    @7
    wb
    vy
    vex
    vx
    @5
    cA
    @1
    cvv
    eliin
    ax-mp
    @5
    cB
    @3
    eldif
    3bitr4g
    eqrdv
end
