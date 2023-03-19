include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cmin.mm"
include "cfzo.mm"
include "cop.mm"
include "csubstr.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "swrdf.mm"
include "frn.mm"
include "syl.mm"

theorem swrdrn
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` W ) ) ) -> ran ( W substr <. M , N >. ) C_ V )

  proof
    cW
    cV
    cword
    wcel
    cM
    cc0
    cN
    cfz
    co
    wcel
    cN
    cc0
    cW
    chash
    cfv
    cfz
    co
    wcel
    w3a
    cc0
    cN
    cM
    cmin
    co
    cfzo
    co
    #
    cV
    cW
    cM
    cN
    cop
    csubstr
    co
    #
    wf
    @1
    crn
    cV
    wss
    cM
    cN
    cV
    cW
    swrdf
    @0
    cV
    @1
    frn
    syl
end
