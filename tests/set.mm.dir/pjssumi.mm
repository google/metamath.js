include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "cpjh.mm"
include "chj.mm"
include "chos.mm"
include "osumi.mm"
include "fveq2d.mm"
include "pjscji.mm"
include "eqtrd.mm"

theorem pjssumi
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( G C_ ( _|_ ` H ) -> ( projh ` ( G +H H ) ) = ( ( projh ` G ) +op ( projh ` H ) ) )

  proof
    cG
    cH
    cort
    cfv
    wss
    #
    cG
    cH
    cph
    co
    #
    cpjh
    cfv
    cG
    cH
    chj
    co
    #
    cpjh
    cfv
    cG
    cpjh
    cfv
    cH
    cpjh
    cfv
    chos
    co
    @0
    @1
    @2
    cpjh
    cG
    cH
    pjco.1
    pjco.2
    osumi
    fveq2d
    cG
    cH
    pjco.1
    pjco.2
    pjscji
    eqtrd
end
