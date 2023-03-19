include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cn0.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cdvds.mm"
include "wa.mm"
include "wb.mm"
include "divalgmod.mm"
include "baibd.mm"
include "3impa.mm"

theorem divalgmodcl
  let cD: class D
  let cR: class R
  let cN: class N


  assert |- ( ( N e. ZZ /\ D e. NN /\ R e. NN0 ) -> ( R = ( N mod D ) <-> ( R < D /\ D || ( N - R ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    cR
    cn0
    wcel
    #
    cR
    cN
    cD
    cmo
    co
    wceq
    #
    cR
    cD
    clt
    wbr
    cD
    cN
    cR
    cmin
    co
    cdvds
    wbr
    wa
    #
    wb
    @0
    @1
    wa
    @3
    @2
    @4
    cD
    cR
    cN
    divalgmod
    baibd
    3impa
end
