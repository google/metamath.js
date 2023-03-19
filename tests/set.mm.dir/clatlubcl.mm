include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cglb.mm"
include "eqid.mm"
include "clatlem.mm"
include "simpld.mm"

theorem clatlubcl
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  assume clatlubcl.b: |- B = ( Base ` K )
  assume clatlubcl.u: |- U = ( lub ` K )


  assert |- ( ( K e. CLat /\ S C_ B ) -> ( U ` S ) e. B )

  proof
    cK
    ccla
    wcel
    cS
    cB
    wss
    wa
    cS
    cU
    cfv
    cB
    wcel
    cS
    cK
    cglb
    cfv
    #
    cfv
    cB
    wcel
    cB
    cS
    cU
    @0
    cK
    clatlubcl.b
    clatlubcl.u
    @0
    eqid
    clatlem
    simpld
end
