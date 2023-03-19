include "chlo.mm"
include "wcel.mm"
include "chil.mm"
include "c0v.mm"
include "wne.mm"
include "cc0.mm"
include "csp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "cba.mm"
include "cfv.mm"
include "df-hba.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "cn0v.mm"
include "df-h0v.mm"
include "hlipgt0.mm"
include "mp3an1.mm"

theorem axhis4-zf
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  assume axhil.1: |- U = <. <. +h , .h >. , normh >.
  assume axhil.2: |- U e. CHilOLD
  assume axhfi.1: |- .ih = ( .iOLD ` U )


  assert |- ( ( A e. ~H /\ A =/= 0h ) -> 0 < ( A .ih A ) )

  proof
    cU
    chlo
    wcel
    cA
    chil
    wcel
    cA
    c0v
    wne
    cc0
    cA
    cA
    csp
    co
    clt
    wbr
    axhil.2
    cA
    csp
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
    axhfi.1
    hlipgt0
    mp3an1
end
