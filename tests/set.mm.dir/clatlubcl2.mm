include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "adantl.mm"
include "wceq.mm"
include "cpo.mm"
include "cglb.mm"
include "eqid.mm"
include "isclat.mm"
include "simprl.mm"
include "sylbi.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem clatlubcl2
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  assume clatlubcl.b: |- B = ( Base ` K )
  assume clatlubcl.u: |- U = ( lub ` K )


  assert |- ( ( K e. CLat /\ S C_ B ) -> S e. dom U )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    wa
    cS
    cB
    cpw
    #
    cU
    cdm
    #
    @1
    cS
    @2
    wcel
    #
    @0
    @4
    @1
    cS
    cB
    cB
    cK
    cbs
    cfv
    cvv
    clatlubcl.b
    cK
    cbs
    fvex
    eqeltri
    elpw2
    biimpri
    adantl
    @0
    @3
    @2
    wceq
    #
    @1
    @0
    cK
    cpo
    wcel
    #
    @5
    cK
    cglb
    cfv
    #
    cdm
    @2
    wceq
    #
    wa
    wa
    @5
    cB
    cU
    @7
    cK
    clatlubcl.b
    clatlubcl.u
    @7
    eqid
    isclat
    @6
    @5
    @8
    simprl
    sylbi
    adantr
    eleqtrrd
end
