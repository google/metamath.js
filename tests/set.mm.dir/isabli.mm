include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "rgen2a.mm"
include "isabl2.mm"
include "mpbir2an.mm"

theorem isabli
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume isabli.g: |- G e. Grp
  assume isabli.b: |- B = ( Base ` G )
  assume isabli.p: |- .+ = ( +g ` G )
  assume isabli.c: |- ( ( x e. B /\ y e. B ) -> ( x .+ y ) = ( y .+ x ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  assert |- G e. Abel

  proof
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @1
    @0
    c.pl
    co
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    isabli.g
    @2
    vx
    vy
    cB
    isabli.c
    rgen2a
    vx
    vy
    cB
    c.pl
    cG
    isabli.b
    isabli.p
    isabl2
    mpbir2an
end
