include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "wceq.mm"
include "lmodgrp.mm"
include "grpsubid.mm"
include "sylan.mm"

theorem lmodsubid
  let cA: class A
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lmodsubeq0.v: |- V = ( Base ` W )
  assume lmodsubeq0.o: |- .0. = ( 0g ` W )
  assume lmodsubeq0.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ A e. V ) -> ( A .- A ) = .0. )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cA
    cV
    wcel
    cA
    cA
    c.mi
    co
    c.0
    wceq
    cW
    lmodgrp
    cV
    cW
    c.mi
    cA
    c.0
    lmodsubeq0.v
    lmodsubeq0.o
    lmodsubeq0.m
    grpsubid
    sylan
end
