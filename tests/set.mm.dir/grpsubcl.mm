include "cgrp.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "co.mm"
include "grpsubf.mm"
include "fovrn.mm"
include "syl3an1.mm"

theorem grpsubcl
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume grpsubcl.b: |- B = ( Base ` G )
  assume grpsubcl.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( X .- Y ) e. B )

  proof
    cG
    cgrp
    wcel
    cB
    cB
    cxp
    cB
    c.mi
    wf
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    c.mi
    co
    cB
    wcel
    cB
    cG
    c.mi
    grpsubcl.b
    grpsubcl.m
    grpsubf
    cX
    cY
    cB
    cB
    cB
    c.mi
    fovrn
    syl3an1
end
