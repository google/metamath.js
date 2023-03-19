include "cn0.mm"
include "wcel.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c3.mm"
include "cuz.mm"
include "c2.mm"
include "cn.mm"
include "fmtnoge3.mm"
include "uzuzle23.mm"
include "eluz2nn.mm"
include "3syl.mm"

theorem fmtnonn
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( FermatNo ` N ) e. NN )

  proof
    cN
    cn0
    wcel
    cN
    cfmtno
    cfv
    #
    c3
    cuz
    cfv
    wcel
    @0
    c2
    cuz
    cfv
    wcel
    @0
    cn
    wcel
    cN
    fmtnoge3
    @0
    uzuzle23
    @0
    eluz2nn
    3syl
end
