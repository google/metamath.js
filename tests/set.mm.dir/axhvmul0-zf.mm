include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "cc0.mm"
include "csm.mm"
include "co.mm"
include "c0v.mm"
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
include "cn0v.mm"
include "df-h0v.mm"
include "hlmul0.mm"
include "mpan.mm"

theorem axhvmul0-zf
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( A e. ~H -> ( 0 .h A ) = 0h )

  proof
    cU
    chlo
    wcel
    cA
    chil
    wcel
    cc0
    cA
    csm
    co
    c0v
    wceq
    axhil.2
    cA
    csm
    cU
    chil
    c0v
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
    c0v
    @0
    cn0v
    cfv
    cU
    cn0v
    cfv
    df-h0v
    cU
    @0
    cn0v
    axhil.1
    fveq2i
    eqtr4i
    hlmul0
    mpan
end
