include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "clsw.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c0.mm"
include "lsw.mm"
include "adantr.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "cdm.mm"
include "cfzo.mm"
include "wn.mm"
include "wrddm.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "1nn.mm"
include "nnnle0.mm"
include "ax-mp.mm"
include "0re.mm"
include "1re.mm"
include "subge0i.mm"
include "mtbir.mm"
include "elfzole1.mm"
include "mto.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "ndmfv.mm"
include "3syl.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"

theorem lsw0
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 0 ) -> ( lastS ` W ) = (/) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cc0
    wceq
    #
    wa
    cW
    clsw
    cfv
    #
    @2
    c1
    cmin
    co
    #
    cW
    cfv
    #
    c0
    @1
    @4
    @6
    wceq
    @3
    cW
    @0
    lsw
    adantr
    @3
    @1
    @6
    cc0
    c1
    cmin
    co
    #
    cW
    cfv
    #
    c0
    @3
    @5
    @7
    cW
    @2
    cc0
    c1
    cmin
    oveq1
    fveq2d
    @1
    cW
    cdm
    #
    cc0
    @2
    cfzo
    co
    #
    wceq
    #
    @7
    @9
    wcel
    #
    wn
    @8
    c0
    wceq
    cV
    cW
    wrddm
    @11
    @12
    @7
    @10
    wcel
    #
    @13
    cc0
    @7
    cle
    wbr
    #
    @14
    c1
    cc0
    cle
    wbr
    #
    c1
    cn
    wcel
    @15
    wn
    1nn
    c1
    nnnle0
    ax-mp
    cc0
    c1
    0re
    1re
    subge0i
    mtbir
    @7
    cc0
    @2
    elfzole1
    mto
    @9
    @10
    @7
    eleq2
    mtbiri
    @7
    cW
    ndmfv
    3syl
    sylan9eqr
    eqtrd
end
