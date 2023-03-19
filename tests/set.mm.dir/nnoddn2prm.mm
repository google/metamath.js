include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "wi.mm"
include "oddprm.mm"
include "cz.mm"
include "nnz.mm"
include "wb.mm"
include "oddm1d2.mm"
include "syl5ibrcom.mm"
include "jcai.mm"

theorem nnoddn2prm
  let cN: class N


  assert |- ( N e. ( Prime \ { 2 } ) -> ( N e. NN /\ -. 2 || N ) )

  proof
    cN
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    @1
    cN
    cprime
    wcel
    @2
    cN
    cprime
    @0
    eldifi
    cN
    prmnn
    syl
    @1
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @2
    @3
    wi
    cN
    oddprm
    @5
    @3
    @2
    @4
    cz
    wcel
    #
    @4
    nnz
    @2
    cN
    cz
    wcel
    @3
    @6
    wb
    cN
    nnz
    cN
    oddm1d2
    syl
    syl5ibrcom
    syl
    jcai
end
