include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "cn0.mm"
include "wral.mm"
include "crio.mm"
include "cfv.mm"
include "odcl.mm"
include "adantl.mm"
include "odeq.mm"
include "3expa.mm"
include "bicomd.mm"
include "riota5.mm"
include "eqcomd.mm"

theorem odval2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )

  disjoint .0. y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint .x. y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint N y
  disjoint x z
  disjoint G z
  assert |- ( ( G e. Grp /\ A e. X ) -> ( O ` A ) = ( iota_ x e. NN0 A. y e. NN0 ( x || y <-> ( y .x. A ) = .0. ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cdvds
    wbr
    @4
    cA
    c.x
    co
    c.0
    wceq
    wb
    vy
    cn0
    wral
    #
    vx
    cn0
    crio
    cA
    cO
    cfv
    #
    @2
    @5
    vx
    cn0
    @6
    @1
    @6
    cn0
    wcel
    @0
    cA
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    adantl
    @2
    @3
    cn0
    wcel
    #
    wa
    @3
    @6
    wceq
    #
    @5
    @0
    @1
    @7
    @8
    @5
    wb
    vy
    cA
    c.x
    cG
    @3
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odeq
    3expa
    bicomd
    riota5
    eqcomd
end
