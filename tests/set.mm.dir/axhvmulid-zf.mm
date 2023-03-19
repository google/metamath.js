include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "c1.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cva.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlnvi.mm"
include "h2hsm.mm"
include "hlmulid.mm"
include "mpan.mm"

theorem axhvmulid-zf
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( A e. ~H -> ( 1 .h A ) = A )

  proof
    cU
    chlo
    wcel
    cA
    chil
    wcel
    c1
    cA
    csm
    co
    cA
    wceq
    axhil.2
    cA
    csm
    cU
    chil
    chil
    cva
    csm
    cop
    cno
    cop
    #
    cba
    cfv
    cU
    cba
    cfv
    df-hba
    cU
    @0
    cba
    axhil.1
    fveq2i
    eqtr4i
    cU
    axhil.1
    cU
    axhil.2
    hlnvi
    h2hsm
    hlmulid
    mpan
end
