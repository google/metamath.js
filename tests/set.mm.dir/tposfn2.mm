include "wrel.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "ctpos.mm"
include "ccnv.mm"
include "wfn.mm"
include "wi.mm"
include "tposfun.mm"
include "a1i.mm"
include "dmtpos.mm"
include "releq.mm"
include "cnveq.mm"
include "eqeq2d.mm"
include "3imtr3d.mm"
include "com12.mm"
include "anim12d.mm"
include "df-fn.mm"
include "3imtr4g.mm"

theorem tposfn2
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel A -> ( F Fn A -> tpos F Fn `' A ) )

  proof
    cA
    wrel
    #
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    cF
    ctpos
    #
    wfun
    #
    @4
    cdm
    #
    cA
    ccnv
    #
    wceq
    #
    wa
    cF
    cA
    wfn
    @4
    @7
    wfn
    @0
    @1
    @5
    @3
    @8
    @1
    @5
    wi
    @0
    cF
    tposfun
    a1i
    @3
    @0
    @8
    @3
    @2
    wrel
    #
    @6
    @2
    ccnv
    #
    wceq
    #
    @0
    @8
    @9
    @11
    wi
    @3
    cF
    dmtpos
    a1i
    @2
    cA
    releq
    @3
    @10
    @7
    @6
    @2
    cA
    cnveq
    eqeq2d
    3imtr3d
    com12
    anim12d
    cF
    cA
    df-fn
    @4
    @7
    df-fn
    3imtr4g
end
