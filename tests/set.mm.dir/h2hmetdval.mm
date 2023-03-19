include "cnv.mm"
include "wcel.mm"
include "chil.mm"
include "co.mm"
include "cmv.mm"
include "cno.mm"
include "cfv.mm"
include "wceq.mm"
include "h2hvs.mm"
include "h2hnm.mm"
include "imsdval.mm"
include "mp3an1.mm"

theorem h2hmetdval
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  assume h2h.1: |- U = <. <. +h , .h >. , normh >.
  assume h2h.2: |- U e. NrmCVec
  assume h2hm.4: |- ~H = ( BaseSet ` U )
  assume h2hm.5: |- D = ( IndMet ` U )


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A D B ) = ( normh ` ( A -h B ) ) )

  proof
    cU
    cnv
    wcel
    cA
    chil
    wcel
    cB
    chil
    wcel
    cA
    cB
    cD
    co
    cA
    cB
    cmv
    co
    cno
    cfv
    wceq
    h2h.2
    cA
    cB
    cD
    cU
    cmv
    cno
    chil
    h2hm.4
    cU
    h2h.1
    h2h.2
    h2hm.4
    h2hvs
    cU
    h2h.1
    h2h.2
    h2hnm
    h2hm.5
    imsdval
    mp3an1
end
