include "wcel.mm"
include "wceq.mm"
include "wal.mm"
include "csb.mm"
include "wi.mm"
include "wsbc.mm"
include "wb.mm"
include "idn1.mm"
include "spsbc.mm"
include "e1a.mm"
include "sbceqg.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "e11.mm"
include "in1.mm"

theorem csbeq2gVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( A. x B = C -> [_ A / x ]_ B = [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    wceq
    #
    vx
    wal
    #
    vx
    cA
    cB
    csb
    vx
    cA
    cC
    csb
    wceq
    #
    wi
    #
    @0
    @2
    @1
    vx
    cA
    wsbc
    #
    wi
    #
    @5
    @3
    wb
    #
    @4
    @0
    @0
    @6
    @0
    idn1
    #
    @1
    vx
    cA
    cV
    spsbc
    e1a
    @0
    @0
    @7
    @8
    vx
    cA
    cB
    cC
    cV
    sbceqg
    e1a
    @7
    @6
    @4
    @5
    @3
    @2
    imbi2
    biimpcd
    e11
    in1
end
