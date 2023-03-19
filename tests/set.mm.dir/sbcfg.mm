include "wcel.mm"
include "wf.mm"
include "wsbc.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "csb.mm"
include "wb.mm"
include "df-f.mm"
include "a1i.mm"
include "sbcbidv.mm"
include "sbcfng.mm"
include "sbcssg.mm"
include "csbrn.mm"
include "sseq1i.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "sbcan.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem sbcfg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cX: class X

  disjoint V x
  disjoint X x
  assert |- ( X e. V -> ( [. X / x ]. F : A --> B <-> [_ X / x ]_ F : [_ X / x ]_ A --> [_ X / x ]_ B ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cB
    cF
    wf
    #
    vx
    cX
    wsbc
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    wa
    #
    vx
    cX
    wsbc
    #
    vx
    cX
    cA
    csb
    #
    vx
    cX
    cB
    csb
    #
    vx
    cX
    cF
    csb
    #
    wf
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
    cA
    cB
    cF
    df-f
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
    @9
    @7
    wfn
    #
    @9
    crn
    #
    @8
    wss
    #
    wa
    @6
    @10
    @0
    @11
    @13
    @12
    @15
    vx
    cA
    cF
    cV
    cX
    sbcfng
    @0
    @12
    vx
    cX
    @3
    csb
    #
    @8
    wss
    @15
    vx
    cX
    @3
    cB
    cV
    sbcssg
    @16
    @14
    @8
    vx
    cX
    cF
    csbrn
    sseq1i
    syl6bb
    anbi12d
    @2
    @4
    vx
    cX
    sbcan
    @7
    @8
    @9
    df-f
    3bitr4g
    bitrd
end
