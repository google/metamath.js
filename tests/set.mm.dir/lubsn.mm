include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "cjn.mm"
include "co.mm"
include "cpr.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "joinval.mm"
include "dfsn2.mm"
include "fveq2i.mm"
include "syl6reqr.mm"
include "latjidm.mm"
include "eqtrd.mm"

theorem lubsn
  let cB: class B
  let cU: class U
  let cK: class K
  let cX: class X
  assume lubsn.b: |- B = ( Base ` K )
  assume lubsn.u: |- U = ( lub ` K )


  assert |- ( ( K e. Lat /\ X e. B ) -> ( U ` { X } ) = X )

  proof
    cK
    clat
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    csn
    #
    cU
    cfv
    #
    cX
    cX
    cK
    cjn
    cfv
    #
    co
    #
    cX
    @2
    @6
    cX
    cX
    cpr
    #
    cU
    cfv
    @4
    @2
    cU
    @5
    cK
    clat
    cB
    cX
    cX
    cB
    lubsn.u
    @5
    eqid
    #
    @0
    @1
    simpl
    @0
    @1
    simpr
    #
    @9
    joinval
    @3
    @7
    cU
    cX
    dfsn2
    fveq2i
    syl6reqr
    cB
    @5
    cK
    cX
    lubsn.b
    @8
    latjidm
    eqtrd
end
