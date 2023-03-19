include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem dmressnsn
  let cA: class A
  let cF: class F


  assert |- ( A e. dom F -> dom ( F |` { A } ) = { A } )

  proof
    cA
    cF
    cdm
    #
    wcel
    #
    cF
    cA
    csn
    #
    cres
    cdm
    @2
    @0
    cin
    #
    @2
    cF
    @2
    dmres
    @1
    @2
    @0
    wss
    @3
    @2
    wceq
    cA
    @0
    snssi
    @2
    @0
    df-ss
    sylib
    syl5eq
end
