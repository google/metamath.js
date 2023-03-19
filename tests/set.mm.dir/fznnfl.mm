include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "wb.mm"
include "flcl.mm"
include "fznn.mm"
include "syl.mm"
include "nnz.mm"
include "flge.mm"
include "sylan2.mm"
include "pm5.32da.mm"
include "bitr4d.mm"

theorem fznnfl
  let cK: class K
  let cN: class N


  assert |- ( N e. RR -> ( K e. ( 1 ... ( |_ ` N ) ) <-> ( K e. NN /\ K <_ N ) ) )

  proof
    cN
    cr
    wcel
    #
    cK
    c1
    cN
    cfl
    cfv
    #
    cfz
    co
    wcel
    #
    cK
    cn
    wcel
    #
    cK
    @1
    cle
    wbr
    #
    wa
    #
    @3
    cK
    cN
    cle
    wbr
    #
    wa
    @0
    @1
    cz
    wcel
    @2
    @5
    wb
    cN
    flcl
    cK
    @1
    fznn
    syl
    @0
    @3
    @6
    @4
    @3
    @0
    cK
    cz
    wcel
    @6
    @4
    wb
    cK
    nnz
    cN
    cK
    flge
    sylan2
    pm5.32da
    bitr4d
end
