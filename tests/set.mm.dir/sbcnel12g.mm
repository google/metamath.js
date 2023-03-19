include "wcel.mm"
include "wn.mm"
include "wsbc.mm"
include "wnel.mm"
include "csb.mm"
include "sbcng.mm"
include "df-nel.mm"
include "sbcbii.mm"
include "sbcel12.mm"
include "xchbinxr.mm"
include "3bitr4g.mm"

theorem sbcnel12g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( [. A / x ]. B e/ C <-> [_ A / x ]_ B e/ [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    cB
    cC
    wcel
    #
    wn
    #
    vx
    cA
    wsbc
    @0
    vx
    cA
    wsbc
    #
    wn
    cB
    cC
    wnel
    #
    vx
    cA
    wsbc
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    wnel
    #
    @0
    vx
    cA
    cV
    sbcng
    @3
    @1
    vx
    cA
    cB
    cC
    df-nel
    sbcbii
    @6
    @4
    @5
    wcel
    @2
    @4
    @5
    df-nel
    vx
    cA
    cB
    cC
    sbcel12
    xchbinxr
    3bitr4g
end
