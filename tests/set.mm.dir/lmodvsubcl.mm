include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "co.mm"
include "lmodgrp.mm"
include "grpsubcl.mm"
include "syl3an1.mm"

theorem lmodvsubcl
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodvsubcl.v: |- V = ( Base ` W )
  assume lmodvsubcl.m: |- .- = ( -g ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ Y e. V ) -> ( X .- Y ) e. V )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    cX
    cY
    c.mi
    co
    cV
    wcel
    cW
    lmodgrp
    cV
    cW
    c.mi
    cX
    cY
    lmodvsubcl.v
    lmodvsubcl.m
    grpsubcl
    syl3an1
end
