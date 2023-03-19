include "wcel.mm"
include "wfn.mm"
include "wsbc.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "csb.mm"
include "wb.mm"
include "df-fn.mm"
include "a1i.mm"
include "sbcbidv.mm"
include "sbcfung.mm"
include "sbceqg.mm"
include "csbdm.mm"
include "eqeq1i.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "sbcan.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem sbcfng
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X

  disjoint V x
  disjoint X x
  assert |- ( X e. V -> ( [. X / x ]. F Fn A <-> [_ X / x ]_ F Fn [_ X / x ]_ A ) )

  proof
    cX
    cV
    wcel
    #
    cF
    cA
    wfn
    #
    vx
    cX
    wsbc
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
    #
    vx
    cX
    wsbc
    #
    vx
    cX
    cF
    csb
    #
    vx
    cX
    cA
    csb
    #
    wfn
    #
    @0
    @1
    @5
    vx
    cX
    @1
    @5
    wb
    @0
    cF
    cA
    df-fn
    a1i
    sbcbidv
    @0
    @2
    vx
    cX
    wsbc
    #
    @4
    vx
    cX
    wsbc
    #
    wa
    @7
    wfun
    #
    @7
    cdm
    #
    @8
    wceq
    #
    wa
    @6
    @9
    @0
    @10
    @12
    @11
    @14
    vx
    cX
    cF
    cV
    sbcfung
    @0
    @11
    vx
    cX
    @3
    csb
    #
    @8
    wceq
    @14
    vx
    cX
    @3
    cA
    cV
    sbceqg
    @15
    @13
    @8
    vx
    cX
    cF
    csbdm
    eqeq1i
    syl6bb
    anbi12d
    @2
    @4
    vx
    cX
    sbcan
    @7
    @8
    df-fn
    3bitr4g
    bitrd
end
