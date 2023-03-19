include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cgrrflx.mm"
include "syl3anc.mm"

theorem cgrrflxd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  assume cgrrflxd.1: |- ( ph -> N e. NN )
  assume cgrrflxd.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrrflxd.3: |- ( ph -> B e. ( EE ` N ) )


  assert |- ( ph -> <. A , B >. Cgr <. A , B >. )

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
    #
    @1
    ccgr
    wbr
    cgrrflxd.1
    cgrrflxd.2
    cgrrflxd.3
    cA
    cB
    cN
    cgrrflx
    syl3anc
end
