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
include "wfn.mm"
include "swrdf.mm"
include "ffn.mm"
include "syl.mm"

theorem swrdvalfn
  let cS: class S
  let cF: class F
  let cL: class L
  let cV: class V


  assert |- ( ( S e. Word V /\ F e. ( 0 ... L ) /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S substr <. F , L >. ) Fn ( 0 ..^ ( L - F ) ) )

  proof
    cS
    cV
    cword
    wcel
    cF
    cc0
    cL
    cfz
    co
    wcel
    cL
    cc0
    cS
    chash
    cfv
    cfz
    co
    wcel
    w3a
    cc0
    cL
    cF
    cmin
    co
    cfzo
    co
    #
    cV
    cS
    cF
    cL
    cop
    csubstr
    co
    #
    wf
    @1
    @0
    wfn
    cF
    cL
    cV
    cS
    swrdf
    @0
    cV
    @1
    ffn
    syl
end
