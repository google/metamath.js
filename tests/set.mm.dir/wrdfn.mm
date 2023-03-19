include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "wrdf.mm"
include "ffn.mm"
include "syl.mm"

theorem wrdfn
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> W Fn ( 0 ..^ ( # ` W ) ) )

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
    @0
    wfn
    cS
    cW
    wrdf
    @0
    cS
    cW
    ffn
    syl
end
