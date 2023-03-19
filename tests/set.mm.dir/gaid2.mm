include "cgrp.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cga.mm"
include "csubg.mm"
include "cfv.mm"
include "subgid.mm"
include "eqid.mm"
include "subgga.mm"
include "syl.mm"
include "ressid.mm"
include "oveq1d.mm"
include "eleqtrd.mm"

theorem gaid2
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cX: class X
  assume gaid2.1: |- X = ( Base ` G )
  assume gaid2.2: |- .+ = ( +g ` G )
  assume gaid2.3: |- F = ( x e. X , y e. X |-> ( x .+ y ) )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  assert |- ( G e. Grp -> F e. ( G GrpAct X ) )

  proof
    cG
    cgrp
    wcel
    #
    cF
    cG
    cX
    cress
    co
    #
    cX
    cga
    co
    #
    cG
    cX
    cga
    co
    @0
    cX
    cG
    csubg
    cfv
    wcel
    cF
    @2
    wcel
    cX
    cG
    gaid2.1
    subgid
    vx
    vy
    c.pl
    cF
    cG
    @1
    cX
    cX
    gaid2.1
    gaid2.2
    @1
    eqid
    gaid2.3
    subgga
    syl
    @0
    @1
    cG
    cX
    cga
    cX
    cG
    cgrp
    gaid2.1
    ressid
    oveq1d
    eleqtrd
end
