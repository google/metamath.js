include "cst.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "cin.mm"
include "wa.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "choccli.mm"
include "chincli.mm"
include "pm3.2i.mm"
include "inss1.mm"
include "chsscon3i.mm"
include "mpbi.mm"
include "stj.mm"
include "mp2ani.mm"

theorem stji1i
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( S ` ( ( _|_ ` A ) vH ( A i^i B ) ) ) = ( ( S ` ( _|_ ` A ) ) + ( S ` ( A i^i B ) ) ) )

  proof
    cS
    cst
    wcel
    cA
    cort
    cfv
    #
    cch
    wcel
    #
    cA
    cB
    cin
    #
    cch
    wcel
    #
    wa
    @0
    @2
    cort
    cfv
    wss
    #
    @0
    @2
    chj
    co
    cS
    cfv
    @0
    cS
    cfv
    @2
    cS
    cfv
    caddc
    co
    wceq
    @1
    @3
    cA
    stle.1
    choccli
    cA
    cB
    stle.1
    stle.2
    chincli
    #
    pm3.2i
    @2
    cA
    wss
    @4
    cA
    cB
    inss1
    @2
    cA
    @5
    stle.1
    chsscon3i
    mpbi
    @0
    @2
    cS
    stj
    mp2ani
end
