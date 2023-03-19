include "cword.mm"
include "wcel.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "syl.mm"

theorem lencl
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> ( # ` W ) e. NN0 )

  proof
    cW
    cS
    cword
    wcel
    cW
    cfn
    wcel
    cW
    chash
    cfv
    cn0
    wcel
    cS
    cW
    wrdfin
    cW
    hashcl
    syl
end
