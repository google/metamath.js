include "cuhgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "c2.mm"
include "cbc.mm"
include "co.mm"
include "uhgr0vsize0.mm"
include "oveq1.mm"
include "cn.mm"
include "2nn.mm"
include "bc0k.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem cusgrsizeindb0
  let cE: class E
  let cG: class G
  let cV: class V
  assume cusgrsizeindb0.v: |- V = ( Vtx ` G )
  assume cusgrsizeindb0.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UHGraph /\ ( # ` V ) = 0 ) -> ( # ` E ) = ( ( # ` V ) _C 2 ) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    chash
    cfv
    #
    cc0
    wceq
    #
    wa
    cE
    chash
    cfv
    cc0
    @1
    c2
    cbc
    co
    #
    cE
    cG
    cV
    cusgrsizeindb0.v
    cusgrsizeindb0.e
    uhgr0vsize0
    @2
    cc0
    @3
    wceq
    @0
    @2
    @3
    cc0
    c2
    cbc
    co
    #
    cc0
    @1
    cc0
    c2
    cbc
    oveq1
    c2
    cn
    wcel
    @4
    cc0
    wceq
    2nn
    c2
    bc0k
    ax-mp
    syl6req
    adantl
    eqtrd
end
