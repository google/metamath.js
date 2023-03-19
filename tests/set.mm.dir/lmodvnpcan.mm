include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "wceq.mm"
include "lmodgrp.mm"
include "grpnpcan.mm"
include "syl3an1.mm"

theorem lmodvnpcan
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.mi: class .-
  let cV: class V
  let cW: class W
  assume lmod4.v: |- V = ( Base ` W )
  assume lmod4.p: |- .+ = ( +g ` W )
  assume lmodvaddsub4.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ A e. V /\ B e. V ) -> ( ( A .- B ) .+ B ) = A )

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
    cB
    c.pl
    co
    cA
    wceq
    cW
    lmodgrp
    cV
    c.pl
    cW
    c.mi
    cA
    cB
    lmod4.v
    lmod4.p
    lmodvaddsub4.m
    grpnpcan
    syl3an1
end
