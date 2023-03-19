include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "csubstr.mm"
include "cfzo.mm"
include "wf.mm"
include "cmin.mm"
include "swrdcl.mm"
include "wrdf.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "swrdlen.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem swrdf
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` W ) ) ) -> ( W substr <. M , N >. ) : ( 0 ..^ ( N - M ) ) --> V )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    cW
    chash
    cfv
    cfz
    co
    wcel
    #
    w3a
    #
    cc0
    cW
    cM
    cN
    cop
    csubstr
    co
    #
    chash
    cfv
    #
    cfzo
    co
    #
    cV
    @5
    wf
    #
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    #
    cV
    @5
    wf
    @1
    @2
    @8
    @3
    @1
    @5
    @0
    wcel
    @8
    cV
    cW
    cM
    cN
    swrdcl
    cV
    @5
    wrdf
    syl
    3ad2ant1
    @4
    @7
    @10
    cV
    @5
    @4
    @6
    @9
    cc0
    cfzo
    cV
    cW
    cM
    cN
    swrdlen
    oveq2d
    feq2d
    mpbid
end
