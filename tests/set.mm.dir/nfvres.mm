include "wcel.mm"
include "wn.mm"
include "cres.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"

theorem nfvres
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( -. A e. B -> ( ( F |` B ) ` A ) = (/) )

  proof
    cA
    cB
    wcel
    #
    wn
    cA
    cF
    cB
    cres
    #
    cdm
    #
    wcel
    #
    wn
    cA
    @1
    cfv
    c0
    wceq
    @3
    @0
    @2
    cB
    cA
    @2
    cB
    cF
    cdm
    #
    cin
    cB
    cF
    cB
    dmres
    cB
    @4
    inss1
    eqsstri
    sseli
    con3i
    cA
    @1
    ndmfv
    syl
end
