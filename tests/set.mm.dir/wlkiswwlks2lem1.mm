include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "wfn.mm"
include "wceq.mm"
include "cn.mm"
include "lencl.mm"
include "elnnnn0c.mm"
include "biimpri.mm"
include "sylan.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "ccnv.mm"
include "fvex.mm"
include "fnmpti.mm"
include "ffzo0hash.mm"
include "sylancl.mm"

theorem wlkiswwlks2lem1
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cV: class V
  assume wlkiswwlks2lem.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) )

  disjoint P x
  assert |- ( ( P e. Word V /\ 1 <_ ( # ` P ) ) -> ( # ` F ) = ( ( # ` P ) - 1 ) )

  proof
    cP
    cV
    cword
    wcel
    #
    c1
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @1
    c1
    cmin
    co
    #
    cn0
    wcel
    #
    cF
    cc0
    @4
    cfzo
    co
    #
    wfn
    cF
    chash
    cfv
    @4
    wceq
    @3
    @1
    cn
    wcel
    #
    @5
    @0
    @1
    cn0
    wcel
    #
    @2
    @7
    cV
    cP
    lencl
    @7
    @8
    @2
    wa
    @1
    elnnnn0c
    biimpri
    sylan
    @1
    nnm1nn0
    syl
    vx
    @6
    vx
    cv
    #
    cP
    cfv
    @9
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    cE
    ccnv
    #
    cfv
    cF
    @10
    @11
    fvex
    wlkiswwlks2lem.f
    fnmpti
    cF
    @4
    ffzo0hash
    sylancl
end
