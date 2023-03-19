include "wcel.mm"
include "cvv.mm"
include "clmat.mm"
include "cfv.mm"
include "c1.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt2.mm"
include "wceq.mm"
include "elex.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "df-lmat.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem lmatval
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cV: class V
  let vm: setvar m

  disjoint M i
  disjoint M j
  disjoint i j
  disjoint M m
  disjoint i m
  disjoint j m
  assert |- ( M e. V -> ( litMat ` M ) = ( i e. ( 1 ... ( # ` M ) ) , j e. ( 1 ... ( # ` ( M ` 0 ) ) ) |-> ( ( M ` ( i - 1 ) ) ` ( j - 1 ) ) ) )

  proof
    cM
    cV
    wcel
    cM
    cvv
    wcel
    cM
    clmat
    cfv
    vi
    vj
    c1
    cM
    chash
    cfv
    #
    cfz
    co
    #
    c1
    cc0
    cM
    cfv
    #
    chash
    cfv
    #
    cfz
    co
    #
    vj
    cv
    c1
    cmin
    co
    #
    vi
    cv
    c1
    cmin
    co
    #
    cM
    cfv
    #
    cfv
    #
    cmpt2
    #
    wceq
    cM
    cV
    elex
    vm
    cM
    vi
    vj
    c1
    vm
    cv
    #
    chash
    cfv
    #
    cfz
    co
    #
    c1
    cc0
    @10
    cfv
    #
    chash
    cfv
    #
    cfz
    co
    #
    @5
    @6
    @10
    cfv
    #
    cfv
    #
    cmpt2
    @9
    cvv
    clmat
    @10
    cM
    wceq
    #
    vi
    vj
    @12
    @15
    @17
    @1
    @4
    @8
    @18
    @11
    @0
    c1
    cfz
    @10
    cM
    chash
    fveq2
    oveq2d
    @18
    @14
    @3
    c1
    cfz
    @18
    @13
    @2
    chash
    cc0
    @10
    cM
    fveq1
    fveq2d
    oveq2d
    @18
    @5
    @16
    @7
    @6
    @10
    cM
    fveq1
    fveq1d
    mpt2eq123dv
    vi
    vj
    vm
    df-lmat
    vi
    vj
    @1
    @4
    @8
    c1
    @0
    cfz
    ovex
    c1
    @3
    cfz
    ovex
    mpt2ex
    fvmpt
    syl
end
