include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "hlnvi.mm"
include "h2hva.mm"
include "cn0v.mm"
include "df-h0v.mm"
include "hladdid.mm"
include "mpan.mm"

theorem axhvaddid-zf
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD


  assert |- ( A e. ~H -> ( A +h 0h ) = A )

  proof
    cU
    chlo
    wcel
    cA
    chil
    wcel
    cA
    c0v
    cva
    co
    cA
    wceq
    axhil.2
    cA
    cU
    cva
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
    h2hva
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
    hladdid
    mpan
end
