include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "grpsubval.mm"
include "grpinvinv.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpsubinv
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume grpsubinv.b: |- B = ( Base ` G )
  assume grpsubinv.p: |- .+ = ( +g ` G )
  assume grpsubinv.m: |- .- = ( -g ` G )
  assume grpsubinv.n: |- N = ( invg ` G )
  assume grpsubinv.g: |- ( ph -> G e. Grp )
  assume grpsubinv.x: |- ( ph -> X e. B )
  assume grpsubinv.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .- ( N ` Y ) ) = ( X .+ Y ) )

  proof
    wph
    cX
    cY
    cN
    cfv
    #
    c.mi
    co
    #
    cX
    @0
    cN
    cfv
    #
    c.pl
    co
    #
    cX
    cY
    c.pl
    co
    wph
    cX
    cB
    wcel
    @0
    cB
    wcel
    #
    @1
    @3
    wceq
    grpsubinv.x
    wph
    cG
    cgrp
    wcel
    #
    cY
    cB
    wcel
    #
    @4
    grpsubinv.g
    grpsubinv.y
    cB
    cG
    cN
    cY
    grpsubinv.b
    grpsubinv.n
    grpinvcl
    syl2anc
    cB
    c.pl
    cG
    cN
    c.mi
    cX
    @0
    grpsubinv.b
    grpsubinv.p
    grpsubinv.n
    grpsubinv.m
    grpsubval
    syl2anc
    wph
    @2
    cY
    cX
    c.pl
    wph
    @5
    @6
    @2
    cY
    wceq
    grpsubinv.g
    grpsubinv.y
    cB
    cG
    cN
    cY
    grpsubinv.b
    grpsubinv.n
    grpinvinv
    syl2anc
    oveq2d
    eqtrd
end
