include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "mrcssv.mm"
include "syl.mm"

theorem mrcssvd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let cX: class X
  assume mrcssd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrcssd.2: |- N = ( mrCls ` A )


  assert |- ( ph -> ( N ` B ) C_ X )

  proof
    wph
    cA
    cX
    cmre
    cfv
    wcel
    cB
    cN
    cfv
    cX
    wss
    mrcssd.1
    cA
    cB
    cN
    cX
    mrcssd.2
    mrcssv
    syl
end
