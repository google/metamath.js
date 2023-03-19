include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cexp.mm"
include "wb.mm"
include "nnz.mm"
include "zesq.mm"
include "syl.mm"
include "nnrp.mm"
include "rphalfcld.mm"
include "rpgt0d.mm"
include "nnsqcl.mm"
include "nnrpd.mm"
include "2thd.mm"
include "anbi12d.mm"
include "elnnz.mm"
include "3bitr4g.mm"

theorem nnesq
  let cN: class N


  assert |- ( N e. NN -> ( ( N / 2 ) e. NN <-> ( ( N ^ 2 ) / 2 ) e. NN ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cc0
    @1
    clt
    wbr
    #
    wa
    cN
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    wa
    @1
    cn
    wcel
    @5
    cn
    wcel
    @0
    @2
    @6
    @3
    @7
    @0
    cN
    cz
    wcel
    @2
    @6
    wb
    cN
    nnz
    cN
    zesq
    syl
    @0
    @3
    @7
    @0
    @1
    @0
    cN
    cN
    nnrp
    rphalfcld
    rpgt0d
    @0
    @5
    @0
    @4
    @0
    @4
    cN
    nnsqcl
    nnrpd
    rphalfcld
    rpgt0d
    2thd
    anbi12d
    @1
    elnnz
    @5
    elnnz
    3bitr4g
end
