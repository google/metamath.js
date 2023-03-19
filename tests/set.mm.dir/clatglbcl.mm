include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "clatlem.mm"
include "simprd.mm"

theorem clatglbcl
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  assume clatglbcl.b: |- B = ( Base ` K )
  assume clatglbcl.g: |- G = ( glb ` K )


  assert |- ( ( K e. CLat /\ S C_ B ) -> ( G ` S ) e. B )

  proof
    cK
    ccla
    wcel
    cS
    cB
    wss
    wa
    cS
    cK
    club
    cfv
    #
    cfv
    cB
    wcel
    cS
    cG
    cfv
    cB
    wcel
    cB
    cS
    @0
    cG
    cK
    clatglbcl.b
    @0
    eqid
    clatglbcl.g
    clatlem
    simprd
end
