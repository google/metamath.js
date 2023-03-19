include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cn.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "posdif.mm"
include "syl2an.mm"
include "zsubcl.mm"
include "ancoms.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "elnnz.mm"
include "syl6bbr.mm"

theorem znnsub
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M < N <-> ( N - M ) e. NN ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    clt
    wbr
    #
    cN
    cM
    cmin
    co
    #
    cz
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    wa
    #
    @4
    cn
    wcel
    @2
    @3
    @6
    @7
    @0
    cM
    cr
    wcel
    cN
    cr
    wcel
    @3
    @6
    wb
    @1
    cM
    zre
    cN
    zre
    cM
    cN
    posdif
    syl2an
    @2
    @5
    @6
    @1
    @0
    @5
    cN
    cM
    zsubcl
    ancoms
    biantrurd
    bitrd
    @4
    elnnz
    syl6bbr
end
