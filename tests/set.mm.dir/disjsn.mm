include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "disj1.mm"
include "con2b.mm"
include "velsn.mm"
include "imbi1i.mm"
include "imnan.mm"
include "3bitri.mm"
include "albii.mm"
include "wex.mm"
include "alnex.mm"
include "df-clel.mm"
include "xchbinxr.mm"

theorem disjsn
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A i^i { B } ) = (/) <-> -. B e. A )

  proof
    cA
    cB
    csn
    #
    cin
    c0
    wceq
    vx
    cv
    #
    cA
    wcel
    #
    @1
    @0
    wcel
    #
    wn
    wi
    #
    vx
    wal
    @1
    cB
    wceq
    #
    @2
    wa
    #
    wn
    #
    vx
    wal
    #
    cB
    cA
    wcel
    #
    wn
    vx
    cA
    @0
    disj1
    @4
    @7
    vx
    @4
    @3
    @2
    wn
    #
    wi
    @5
    @10
    wi
    @7
    @2
    @3
    con2b
    @3
    @5
    @10
    vx
    cB
    velsn
    imbi1i
    @5
    @2
    imnan
    3bitri
    albii
    @8
    @6
    vx
    wex
    @9
    @6
    vx
    alnex
    vx
    cB
    cA
    df-clel
    xchbinxr
    3bitri
end
