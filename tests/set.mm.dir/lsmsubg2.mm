include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "w3a.mm"
include "ccntz.mm"
include "wss.mm"
include "co.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "simp1.mm"
include "ablcntzd.mm"
include "lsmsubg.mm"
include "syl3anc.mm"

theorem lsmsubg2
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  assume lsmcom.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( G e. Abel /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( T .(+) U ) e. ( SubGrp ` G ) )

  proof
    cG
    cabl
    wcel
    #
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @1
    wcel
    #
    w3a
    #
    @2
    @3
    cT
    cU
    cG
    ccntz
    cfv
    #
    cfv
    wss
    cT
    cU
    c.po
    co
    @1
    wcel
    @0
    @2
    @3
    simp2
    #
    @0
    @2
    @3
    simp3
    #
    @4
    cT
    cU
    cG
    @5
    @5
    eqid
    #
    @0
    @2
    @3
    simp1
    @6
    @7
    ablcntzd
    c.po
    cT
    cU
    cG
    @5
    lsmcom.s
    @8
    lsmsubg
    syl3anc
end
