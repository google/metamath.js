include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "eqid.mm"
include "subgss.mm"
include "lsmcomx.mm"
include "syl3an.mm"

theorem lsmcom
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  assume lsmcom.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( G e. Abel /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) -> ( T .(+) U ) = ( U .(+) T ) )

  proof
    cG
    cabl
    wcel
    #
    @0
    cT
    cG
    csubg
    cfv
    #
    wcel
    cT
    cG
    cbs
    cfv
    #
    wss
    cU
    @1
    wcel
    cU
    @2
    wss
    cT
    cU
    c.po
    co
    cU
    cT
    c.po
    co
    wceq
    @0
    id
    @2
    cT
    cG
    @2
    eqid
    #
    subgss
    @2
    cU
    cG
    @3
    subgss
    @2
    c.po
    cT
    cU
    cG
    @3
    lsmcom.s
    lsmcomx
    syl3an
end
