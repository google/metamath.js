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
include "crn.mm"
include "wss.mm"
include "pfxf.mm"
include "frn.mm"
include "syl.mm"

theorem pfxrn
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. ( 0 ... ( # ` W ) ) ) -> ran ( W prefix L ) C_ V )

  proof
    cW
    cV
    cword
    wcel
    cL
    cc0
    cW
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
    cW
    cL
    cpfx
    co
    #
    wf
    @1
    crn
    cV
    wss
    cL
    cV
    cW
    pfxf
    @0
    cV
    @1
    frn
    syl
end
