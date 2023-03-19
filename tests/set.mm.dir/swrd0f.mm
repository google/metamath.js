include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cfzo.mm"
include "cop.mm"
include "csubstr.mm"
include "wf.mm"
include "cmin.mm"
include "simpl.mm"
include "cn0.mm"
include "elfznn0.mm"
include "0elfz.mm"
include "syl.mm"
include "adantl.mm"
include "simpr.mm"
include "swrdf.mm"
include "syl3anc.mm"
include "wceq.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem swrd0f
  let cN: class N
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ N e. ( 0 ... ( # ` W ) ) ) -> ( W substr <. 0 , N >. ) : ( 0 ..^ N ) --> V )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cc0
    cN
    cfzo
    co
    #
    cV
    cW
    cc0
    cN
    cop
    csubstr
    co
    #
    wf
    cc0
    cN
    cc0
    cmin
    co
    #
    cfzo
    co
    #
    cV
    @5
    wf
    #
    @3
    @0
    cc0
    cc0
    cN
    cfz
    co
    wcel
    #
    @2
    @8
    @0
    @2
    simpl
    @2
    @9
    @0
    @2
    cN
    cn0
    wcel
    @9
    cN
    @1
    elfznn0
    #
    cN
    0elfz
    syl
    adantl
    @0
    @2
    simpr
    cc0
    cN
    cV
    cW
    swrdf
    syl3anc
    @3
    @4
    @7
    cV
    @5
    @3
    cN
    @6
    cc0
    cfzo
    @2
    cN
    @6
    wceq
    @0
    @2
    @6
    cN
    @2
    cN
    @2
    cN
    @10
    nn0cnd
    subid1d
    eqcomd
    adantl
    oveq2d
    feq2d
    mpbird
end
