include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "isclwwlkn.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "adantr.mm"
include "sylbi.mm"

theorem clwwlknwrd
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  assume clwwlknwrd.v: |- V = ( Vtx ` G )


  assert |- ( W e. ( N ClWWalksN G ) -> W e. Word V )

  proof
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    cW
    chash
    cfv
    cN
    wceq
    #
    wa
    cW
    cV
    cword
    wcel
    #
    cG
    cN
    cW
    isclwwlkn
    @0
    @2
    @1
    @0
    cG
    cvv
    wcel
    @2
    cW
    c0
    wne
    cG
    cV
    cW
    clwwlknwrd.v
    clwwlkbp
    simp2d
    adantr
    sylbi
end
