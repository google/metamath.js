include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wrdf.mm"
include "cz.mm"
include "wceq.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzoval.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem wrdffz
  let cS: class S
  let cW: class W


  assert |- ( W e. Word S -> W : ( 0 ... ( ( # ` W ) - 1 ) ) --> S )

  proof
    cW
    cS
    cword
    wcel
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    cW
    wf
    cc0
    @1
    c1
    cmin
    co
    cfz
    co
    #
    cS
    cW
    wf
    cS
    cW
    wrdf
    @0
    @2
    @3
    cS
    cW
    @0
    @1
    cz
    wcel
    @2
    @3
    wceq
    @0
    @1
    cS
    cW
    lencl
    nn0zd
    cc0
    @1
    fzoval
    syl
    feq2d
    mpbid
end
