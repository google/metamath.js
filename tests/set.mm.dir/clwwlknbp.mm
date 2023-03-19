include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "clwwlknwrd.mm"
include "clwwlknlen.mm"
include "jca.mm"

theorem clwwlknbp
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume clwwlknwrd.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( N ClWWalksN G ) -> ( W e. Word V /\ ( # ` W ) = N ) )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    cW
    cV
    cword
    wcel
    cW
    chash
    cfv
    cN
    wceq
    cG
    cN
    cV
    cW
    clwwlknwrd.v
    clwwlknwrd
    cG
    cN
    cW
    clwwlknlen
    jca
end
