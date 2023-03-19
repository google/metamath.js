include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "nnz.mm"
include "expm1d.mm"
include "2nn.mm"
include "nnm1nn0.mm"
include "nnexpcld.mm"
include "eqeltrrd.mm"

theorem nnpw2even
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( ( 2 ^ N ) / 2 ) e. NN )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    c1
    cmin
    co
    #
    cexp
    co
    c2
    cN
    cexp
    co
    c2
    cdiv
    co
    cn
    @0
    c2
    cN
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    cN
    nnz
    expm1d
    @0
    c2
    @1
    c2
    cn
    wcel
    @0
    2nn
    a1i
    cN
    nnm1nn0
    nnexpcld
    eqeltrrd
end
