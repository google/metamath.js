include "cgrp.mm"
include "wcel.mm"
include "wtru.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "a1i.mm"
include "cplusg.mm"
include "cv.mm"
include "co.mm"
include "3adant1.mm"
include "w3a.mm"
include "adantl.mm"
include "isgrpd.mm"
include "trud.mm"

theorem isgrpi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume isgrpi.b: |- B = ( Base ` G )
  assume isgrpi.p: |- .+ = ( +g ` G )
  assume isgrpi.c: |- ( ( x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume isgrpi.a: |- ( ( x e. B /\ y e. B /\ z e. B ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume isgrpi.z: |- .0. e. B
  assume isgrpi.i: |- ( x e. B -> ( .0. .+ x ) = x )
  assume isgrpi.n: |- ( x e. B -> N e. B )
  assume isgrpi.j: |- ( x e. B -> ( N .+ x ) = .0. )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N y
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  assert |- G e. Grp

  proof
    cG
    cgrp
    wcel
    wtru
    vx
    vy
    vz
    cB
    c.pl
    cG
    cN
    c.0
    cB
    cG
    cbs
    cfv
    wceq
    wtru
    isgrpi.b
    a1i
    c.pl
    cG
    cplusg
    cfv
    wceq
    wtru
    isgrpi.p
    a1i
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    @0
    @2
    c.pl
    co
    #
    cB
    wcel
    wtru
    isgrpi.c
    3adant1
    @1
    @3
    vz
    cv
    #
    cB
    wcel
    w3a
    @4
    @5
    c.pl
    co
    @0
    @2
    @5
    c.pl
    co
    c.pl
    co
    wceq
    wtru
    isgrpi.a
    adantl
    c.0
    cB
    wcel
    wtru
    isgrpi.z
    a1i
    @1
    c.0
    @0
    c.pl
    co
    @0
    wceq
    wtru
    isgrpi.i
    adantl
    @1
    cN
    cB
    wcel
    wtru
    isgrpi.n
    adantl
    @1
    cN
    @0
    c.pl
    co
    c.0
    wceq
    wtru
    isgrpi.j
    adantl
    isgrpd
    trud
end
