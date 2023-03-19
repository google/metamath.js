include "ccm.mm"
include "wbr.mm"
include "cin.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "incom.mm"
include "fveq2i.mm"
include "pjclem1.mm"
include "wceq.mm"
include "cmcmi.mm"
include "sylbi.mm"
include "3eqtr4a.mm"

theorem pjclem2
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( G C_H H -> ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) )

  proof
    cG
    cH
    ccm
    wbr
    #
    cG
    cH
    cin
    #
    cpjh
    cfv
    cH
    cG
    cin
    #
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    @5
    @4
    ccom
    #
    @1
    @2
    cpjh
    cG
    cH
    incom
    fveq2i
    cG
    cH
    pjclem1.1
    pjclem1.2
    pjclem1
    @0
    cH
    cG
    ccm
    wbr
    @6
    @3
    wceq
    cG
    cH
    pjclem1.1
    pjclem1.2
    cmcmi
    cH
    cG
    pjclem1.2
    pjclem1.1
    pjclem1
    sylbi
    3eqtr4a
end
