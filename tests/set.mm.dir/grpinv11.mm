include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "adantl.mm"
include "cgrp.mm"
include "wcel.mm"
include "grpinvinv.mm"
include "syl2anc.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "impbid1.mm"

theorem grpinv11
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume grpinvinv.b: |- B = ( Base ` G )
  assume grpinvinv.n: |- N = ( invg ` G )
  assume grpinv11.g: |- ( ph -> G e. Grp )
  assume grpinv11.x: |- ( ph -> X e. B )
  assume grpinv11.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( N ` X ) = ( N ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cN
    cfv
    #
    cY
    cN
    cfv
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wph
    @2
    @3
    wph
    @2
    wa
    @0
    cN
    cfv
    #
    @1
    cN
    cfv
    #
    cX
    cY
    @2
    @4
    @5
    wceq
    wph
    @0
    @1
    cN
    fveq2
    adantl
    wph
    @4
    cX
    wceq
    #
    @2
    wph
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    @6
    grpinv11.g
    grpinv11.x
    cB
    cG
    cN
    cX
    grpinvinv.b
    grpinvinv.n
    grpinvinv
    syl2anc
    adantr
    wph
    @5
    cY
    wceq
    #
    @2
    wph
    @7
    cY
    cB
    wcel
    @8
    grpinv11.g
    grpinv11.y
    cB
    cG
    cN
    cY
    grpinvinv.b
    grpinvinv.n
    grpinvinv
    syl2anc
    adantr
    3eqtr3d
    ex
    cX
    cY
    cN
    fveq2
    impbid1
end
