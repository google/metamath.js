include "cdif.mm"
include "ciun.mm"
include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "wral.mm"
include "rexnal.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "xchbinxr.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "eliun.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem iundif2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  assert |- U_ x e. A ( B \ C ) = ( B \ |^|_ x e. A C )

  proof
    vy
    vx
    cA
    cB
    cC
    cdif
    #
    ciun
    #
    cB
    vx
    cA
    cC
    ciin
    #
    cdif
    #
    vy
    cv
    #
    @0
    wcel
    #
    vx
    cA
    wrex
    #
    @4
    cB
    wcel
    #
    @4
    @2
    wcel
    #
    wn
    #
    wa
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    @6
    @7
    @4
    cC
    wcel
    #
    wn
    #
    wa
    #
    vx
    cA
    wrex
    @7
    @12
    vx
    cA
    wrex
    #
    wa
    @10
    @5
    @13
    vx
    cA
    @4
    cB
    cC
    eldif
    rexbii
    @7
    @12
    vx
    cA
    r19.42v
    @14
    @9
    @7
    @14
    @11
    vx
    cA
    wral
    #
    @8
    @11
    vx
    cA
    rexnal
    @4
    cvv
    wcel
    @8
    @15
    wb
    vy
    vex
    vx
    @4
    cA
    cC
    cvv
    eliin
    ax-mp
    xchbinxr
    anbi2i
    3bitri
    vx
    @4
    cA
    @0
    eliun
    @4
    cB
    @2
    eldif
    3bitr4i
    eqriv
end
