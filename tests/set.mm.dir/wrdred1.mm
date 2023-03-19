include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "c1.mm"
include "cmin.mm"
include "cres.mm"
include "wrdf.mm"
include "lencl.mm"
include "wa.mm"
include "wss.mm"
include "cz.mm"
include "nn0z.mm"
include "fzossrbm1.mm"
include "syl.mm"
include "fssres.mm"
include "sylan2.mm"
include "iswrdi.mm"
include "syl2anc.mm"

theorem wrdred1
  let cS: class S
  let cF: class F


  assert |- ( F e. Word S -> ( F |` ( 0 ..^ ( ( # ` F ) - 1 ) ) ) e. Word S )

  proof
    cF
    cS
    cword
    #
    wcel
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    cF
    wf
    #
    @1
    cn0
    wcel
    #
    cF
    cc0
    @1
    c1
    cmin
    co
    #
    cfzo
    co
    #
    cres
    #
    @0
    wcel
    #
    cS
    cF
    wrdf
    cS
    cF
    lencl
    @3
    @4
    wa
    @6
    cS
    @7
    wf
    #
    @8
    @4
    @3
    @6
    @2
    wss
    #
    @9
    @4
    @1
    cz
    wcel
    @10
    @1
    nn0z
    @1
    fzossrbm1
    syl
    @2
    cS
    @6
    cF
    fssres
    sylan2
    cS
    @5
    @7
    iswrdi
    syl
    syl2anc
end
