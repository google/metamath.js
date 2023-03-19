include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "crio.mm"
include "wa.mm"
include "wreu.mm"
include "eqid.mm"
include "grpinveu.mm"
include "riotacl.mm"
include "syl.mm"
include "grpinvfval.mm"
include "fmptd.mm"

theorem grpinvf
  let cB: class B
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume grpinvcl.b: |- B = ( Base ` G )
  assume grpinvcl.n: |- N = ( invg ` G )


  assert |- ( G e. Grp -> N : B --> B )

  proof
    cG
    cgrp
    wcel
    #
    vx
    cB
    vy
    cv
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    vy
    cB
    crio
    #
    cB
    cN
    @0
    @1
    cB
    wcel
    wa
    @4
    vy
    cB
    wreu
    @5
    cB
    wcel
    vy
    cB
    @2
    cG
    @1
    @3
    grpinvcl.b
    @2
    eqid
    #
    @3
    eqid
    #
    grpinveu
    @4
    vy
    cB
    riotacl
    syl
    vx
    vy
    cB
    @2
    cG
    cN
    @3
    grpinvcl.b
    @6
    @7
    grpinvcl.n
    grpinvfval
    fmptd
end
