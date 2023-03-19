include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "axcgrrflx.mm"
include "syl3anc.mm"

theorem cgrrflx2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  assume cgrrflx2d.1: |- ( ph -> N e. NN )
  assume cgrrflx2d.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrrflx2d.3: |- ( ph -> B e. ( EE ` N ) )


  assert |- ( ph -> <. A , B >. Cgr <. B , A >. )

  proof
    wph
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @0
    wcel
    cA
    cB
    cop
    cB
    cA
    cop
    ccgr
    wbr
    cgrrflx2d.1
    cgrrflx2d.2
    cgrrflx2d.3
    cA
    cB
    cN
    axcgrrflx
    syl3anc
end
