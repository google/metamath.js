include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "flle.mm"
include "flge.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "wreu.mm"
include "wb.mm"
include "flcl.mm"
include "zmax.mm"
include "breq1.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbi2and.mm"
include "eqcomd.mm"

theorem flval2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( A e. RR -> ( |_ ` A ) = ( iota_ x e. ZZ ( x <_ A /\ A. y e. ZZ ( y <_ A -> y <_ x ) ) ) )

  proof
    cA
    cr
    wcel
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vy
    cv
    #
    cA
    cle
    wbr
    #
    @3
    @1
    cle
    wbr
    #
    wi
    #
    vy
    cz
    wral
    #
    wa
    #
    vx
    cz
    crio
    #
    cA
    cfl
    cfv
    #
    @0
    @10
    cA
    cle
    wbr
    #
    @4
    @3
    @10
    cle
    wbr
    #
    wi
    #
    vy
    cz
    wral
    #
    @9
    @10
    wceq
    #
    cA
    flle
    @0
    @13
    vy
    cz
    @0
    @3
    cz
    wcel
    wa
    @4
    @12
    cA
    @3
    flge
    biimpd
    ralrimiva
    @0
    @10
    cz
    wcel
    @8
    vx
    cz
    wreu
    @11
    @14
    wa
    #
    @15
    wb
    cA
    flcl
    vx
    vy
    cA
    zmax
    @8
    @16
    vx
    cz
    @10
    @1
    @10
    wceq
    #
    @2
    @11
    @7
    @14
    @1
    @10
    cA
    cle
    breq1
    @17
    @6
    @13
    vy
    cz
    @17
    @5
    @12
    @4
    @1
    @10
    @3
    cle
    breq2
    imbi2d
    ralbidv
    anbi12d
    riota2
    syl2anc
    mpbi2and
    eqcomd
end
