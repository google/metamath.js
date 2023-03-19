include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "wrdf.mm"
include "fdm.mm"
include "syl.mm"

theorem wrddm
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> dom W = ( 0 ..^ ( # ` W ) ) )

  proof
    cW
    cS
    cword
    wcel
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    cS
    cW
    wf
    cW
    cdm
    @0
    wceq
    cS
    cW
    wrdf
    @0
    cS
    cW
    fdm
    syl
end
