include "wrel.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "ccnv.mm"
include "ctpos.mm"
include "wf1o.mm"
include "tposf12.mm"
include "tposfo2.mm"
include "anim12d.mm"
include "df-f1o.mm"
include "3imtr4g.mm"

theorem tposf1o2
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel A -> ( F : A -1-1-onto-> B -> tpos F : `' A -1-1-onto-> B ) )

  proof
    cA
    wrel
    #
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    cA
    ccnv
    #
    cB
    cF
    ctpos
    #
    wf1
    #
    @3
    cB
    @4
    wfo
    #
    wa
    cA
    cB
    cF
    wf1o
    @3
    cB
    @4
    wf1o
    @0
    @1
    @5
    @2
    @6
    cA
    cB
    cF
    tposf12
    cA
    cB
    cF
    tposfo2
    anim12d
    cA
    cB
    cF
    df-f1o
    @3
    cB
    @4
    df-f1o
    3imtr4g
end
