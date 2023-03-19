include "cst.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "chil.mm"
include "caddc.mm"
include "c1.mm"
include "chjoi.mm"
include "fveq2i.mm"
include "cch.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "choccli.mm"
include "pm3.2i.mm"
include "csh.mm"
include "chshii.mm"
include "shococss.mm"
include "ax-mp.mm"
include "stj.mm"
include "mp2ani.mm"
include "sthil.mm"
include "3eqtr3a.mm"

theorem sto1i
  let cA: class A
  let cS: class S
  assume sto1.1: |- A e. CH


  assert |- ( S e. States -> ( ( S ` A ) + ( S ` ( _|_ ` A ) ) ) = 1 )

  proof
    cS
    cst
    wcel
    #
    cA
    cA
    cort
    cfv
    #
    chj
    co
    #
    cS
    cfv
    #
    chil
    cS
    cfv
    cA
    cS
    cfv
    @1
    cS
    cfv
    caddc
    co
    #
    c1
    @2
    chil
    cS
    cA
    sto1.1
    chjoi
    fveq2i
    @0
    cA
    cch
    wcel
    #
    @1
    cch
    wcel
    #
    wa
    cA
    @1
    cort
    cfv
    wss
    #
    @3
    @4
    wceq
    @5
    @6
    sto1.1
    cA
    sto1.1
    choccli
    pm3.2i
    cA
    csh
    wcel
    @7
    cA
    sto1.1
    chshii
    cA
    shococss
    ax-mp
    cA
    @1
    cS
    stj
    mp2ani
    cS
    sthil
    3eqtr3a
end
