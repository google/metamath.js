include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "cpw.mm"
include "ccrd.mm"
include "wceq.mm"
include "com.mm"
include "sneq.mm"
include "fveq2d.mm"
include "pweq.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "cxp.mm"
include "ciun.mm"
include "cfn.mm"
include "cin.mm"
include "ackbij1lem4.mm"
include "ackbij1lem7.mm"
include "syl.mm"
include "vex.mm"
include "xpeq12d.mm"
include "iunxsn.mm"
include "fveq2i.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "vpwex.mm"
include "xpsnen2g.mm"
include "mp2an.mm"
include "carden2b.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "vtoclga.mm"

theorem ackbij1lem8
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. _om -> ( F ` { A } ) = ( card ` ~P A ) )

  proof
    va
    cv
    #
    csn
    #
    cF
    cfv
    #
    @0
    cpw
    #
    ccrd
    cfv
    #
    wceq
    cA
    csn
    #
    cF
    cfv
    #
    cA
    cpw
    #
    ccrd
    cfv
    #
    wceq
    va
    cA
    com
    @0
    cA
    wceq
    #
    @2
    @6
    @4
    @8
    @9
    @1
    @5
    cF
    @0
    cA
    sneq
    fveq2d
    @9
    @3
    @7
    ccrd
    @0
    cA
    pweq
    fveq2d
    eqeq12d
    @0
    com
    wcel
    #
    @2
    vy
    @1
    vy
    cv
    #
    csn
    #
    @11
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    #
    @4
    @10
    @1
    com
    cpw
    cfn
    cin
    wcel
    @2
    @16
    wceq
    @0
    ackbij1lem4
    vx
    vy
    @1
    cF
    ackbij.f
    ackbij1lem7
    syl
    @16
    @1
    @3
    cxp
    #
    ccrd
    cfv
    #
    @4
    @15
    @17
    ccrd
    vy
    @0
    @14
    @17
    va
    vex
    #
    @11
    @0
    wceq
    @12
    @1
    @13
    @3
    @11
    @0
    sneq
    @11
    @0
    pweq
    xpeq12d
    iunxsn
    fveq2i
    @17
    @3
    cen
    wbr
    #
    @18
    @4
    wceq
    @0
    cvv
    wcel
    @3
    cvv
    wcel
    @20
    @19
    va
    vpwex
    @0
    @3
    cvv
    cvv
    xpsnen2g
    mp2an
    @17
    @3
    carden2b
    ax-mp
    eqtri
    syl6eq
    vtoclga
end
