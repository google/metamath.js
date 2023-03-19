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
include "club.mm"
include "eqid.mm"
include "isclat.mm"
include "simprr.mm"
include "sylbi.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem clatglbcl2
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  assume clatglbcl.b: |- B = ( Base ` K )
  assume clatglbcl.g: |- G = ( glb ` K )


  assert |- ( ( K e. CLat /\ S C_ B ) -> S e. dom G )

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
    cG
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
    clatglbcl.b
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
    cK
    club
    cfv
    #
    cdm
    @2
    wceq
    #
    @5
    wa
    wa
    @5
    cB
    @7
    cG
    cK
    clatglbcl.b
    @7
    eqid
    clatglbcl.g
    isclat
    @6
    @8
    @5
    simprr
    sylbi
    adantr
    eleqtrrd
end
