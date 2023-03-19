include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cpfx.mm"
include "wf.mm"
include "wfn.mm"
include "pfxf.mm"
include "ffn.mm"
include "syl.mm"

theorem pfxfn
  let cS: class S
  let cL: class L
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. Word V /\ L e. ( 0 ... ( # ` S ) ) ) -> ( S prefix L ) Fn ( 0 ..^ L ) )

  proof
    cS
    cV
    cword
    wcel
    cL
    cc0
    cS
    chash
    cfv
    cfz
    co
    wcel
    wa
    cc0
    cL
    cfzo
    co
    #
    cV
    cS
    cL
    cpfx
    co
    #
    wf
    @1
    @0
    wfn
    cL
    cV
    cS
    pfxf
    @0
    cV
    @1
    ffn
    syl
end
