include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "lmodgrp.mm"
include "grpsubeq0.mm"
include "syl3an1.mm"

theorem lmodsubeq0
  let cA: class A
  let cB: class B
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lmodsubeq0.v: |- V = ( Base ` W )
  assume lmodsubeq0.o: |- .0. = ( 0g ` W )
  assume lmodsubeq0.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ A e. V /\ B e. V ) -> ( ( A .- B ) = .0. <-> A = B ) )

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
    cB
    cV
    wcel
    cA
    cB
    c.mi
    co
    c.0
    wceq
    cA
    cB
    wceq
    wb
    cW
    lmodgrp
    cV
    cW
    c.mi
    cA
    cB
    c.0
    lmodsubeq0.v
    lmodsubeq0.o
    lmodsubeq0.m
    grpsubeq0
    syl3an1
end
