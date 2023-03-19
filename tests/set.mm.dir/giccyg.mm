include "cgic.mm"
include "wbr.mm"
include "cgim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccyg.mm"
include "wcel.mm"
include "wi.mm"
include "brgic.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wfo.mm"
include "gimghm.mm"
include "wf1o.mm"
include "eqid.mm"
include "gimf1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "ghmcyg.mm"
include "syl2anc.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem giccyg
  let cG: class G
  let cH: class H
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cS: class S
  let c.x: class .x.
  let cX: class X


  assert |- ( G ~=g H -> ( G e. CycGrp -> H e. CycGrp ) )

  proof
    cG
    cH
    cgic
    wbr
    cG
    cH
    cgim
    co
    #
    c0
    wne
    #
    cG
    ccyg
    wcel
    cH
    ccyg
    wcel
    wi
    #
    cG
    cH
    brgic
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    @3
    cG
    cH
    cghm
    co
    wcel
    cG
    cbs
    cfv
    #
    cH
    cbs
    cfv
    #
    @3
    wfo
    #
    @2
    cG
    cH
    @3
    gimghm
    @4
    @5
    @6
    @3
    wf1o
    @7
    @5
    @6
    cG
    cH
    @3
    @5
    eqid
    #
    @6
    eqid
    #
    gimf1o
    @5
    @6
    @3
    f1ofo
    syl
    @5
    @6
    @3
    cG
    cH
    @8
    @9
    ghmcyg
    syl2anc
    exlimiv
    sylbi
    sylbi
end
