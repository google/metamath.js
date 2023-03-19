include "c0.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "fveq2.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "cvv.mm"
include "0ex.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cif.mm"
include "iftrue.mm"
include "fvmpt.mm"
include "ax-mp.mm"

theorem tz7.44-1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cB: class B
  assume tz7.44.1: |- G = ( x e. _V |-> if ( x = (/) , A , if ( Lim dom x , U. ran x , ( H ` ( x ` U. dom x ) ) ) ) )
  assume tz7.44.2: |- ( y e. X -> ( F ` y ) = ( G ` ( F |` y ) ) )
  assume tz7.44-1.3: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G y
  disjoint H x
  disjoint X y
  disjoint B x
  disjoint B y
  assert |- ( (/) e. X -> ( F ` (/) ) = A )

  proof
    c0
    cX
    wcel
    c0
    cF
    cfv
    #
    c0
    cG
    cfv
    #
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cF
    @2
    cres
    #
    cG
    cfv
    #
    wceq
    @0
    @1
    wceq
    vy
    c0
    cX
    @2
    c0
    wceq
    #
    @3
    @0
    @5
    @1
    @2
    c0
    cF
    fveq2
    @6
    @4
    c0
    cG
    @6
    @4
    cF
    c0
    cres
    c0
    @2
    c0
    cF
    reseq2
    cF
    res0
    syl6eq
    fveq2d
    eqeq12d
    tz7.44.2
    vtoclga
    c0
    cvv
    wcel
    @1
    cA
    wceq
    0ex
    vx
    c0
    vx
    cv
    #
    c0
    wceq
    #
    cA
    @7
    cdm
    #
    wlim
    @7
    crn
    cuni
    @9
    cuni
    @7
    cfv
    cH
    cfv
    cif
    #
    cif
    cA
    cvv
    cG
    @8
    cA
    @10
    iftrue
    tz7.44.1
    tz7.44-1.3
    fvmpt
    ax-mp
    syl6eq
end
