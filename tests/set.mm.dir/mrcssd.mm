include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "mrcss.mm"
include "syl3anc.mm"

theorem mrcssd
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cN: class N
  let cV: class V
  let cX: class X
  assume mrcssd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrcssd.2: |- N = ( mrCls ` A )
  assume mrcssd.3: |- ( ph -> U C_ V )
  assume mrcssd.4: |- ( ph -> V C_ X )


  assert |- ( ph -> ( N ` U ) C_ ( N ` V ) )

  proof
    wph
    cA
    cX
    cmre
    cfv
    wcel
    cU
    cV
    wss
    cV
    cX
    wss
    cU
    cN
    cfv
    cV
    cN
    cfv
    wss
    mrcssd.1
    mrcssd.3
    mrcssd.4
    cA
    cU
    cN
    cV
    cX
    mrcssd.2
    mrcss
    syl3anc
end
