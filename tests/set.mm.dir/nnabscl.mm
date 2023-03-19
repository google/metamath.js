include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "zabscl.mm"
include "adantr.mm"
include "cc.mm"
include "wb.mm"
include "zcn.mm"
include "absgt0.mm"
include "syl.mm"
include "biimpa.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem nnabscl
  let cN: class N


  assert |- ( ( N e. ZZ /\ N =/= 0 ) -> ( abs ` N ) e. NN )

  proof
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    cN
    cabs
    cfv
    #
    cz
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @2
    cn
    wcel
    @0
    @3
    @1
    cN
    zabscl
    adantr
    @0
    @1
    @4
    @0
    cN
    cc
    wcel
    @1
    @4
    wb
    cN
    zcn
    cN
    absgt0
    syl
    biimpa
    @2
    elnnz
    sylanbrc
end
