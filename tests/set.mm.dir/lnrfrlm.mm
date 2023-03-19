include "clnr.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "co.mm"
include "clnm.mm"
include "frlmpwsfi.mm"
include "lnrlnm.mm"
include "eqid.mm"
include "pwslnm.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem lnrfrlm
  let cR: class R
  let cI: class I
  let cY: class Y
  assume lnrfrlm.y: |- Y = ( R freeLMod I )


  assert |- ( ( R e. LNoeR /\ I e. Fin ) -> Y e. LNoeM )

  proof
    cR
    clnr
    wcel
    #
    cI
    cfn
    wcel
    #
    wa
    cY
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    clnm
    cR
    cY
    cI
    clnr
    lnrfrlm.y
    frlmpwsfi
    @0
    @2
    clnm
    wcel
    @1
    @3
    clnm
    wcel
    cR
    lnrlnm
    cI
    @2
    @3
    @3
    eqid
    pwslnm
    sylan
    eqeltrd
end
