include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cltrn.mm"
include "eqid.mm"
include "tgrpgrplem.mm"

theorem tgrpgrp
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume tgrpgrp.h: |- H = ( LHyp ` K )
  assume tgrpgrp.g: |- G = ( ( TGrp ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> G e. Grp )

  proof
    cK
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cG
    cH
    cK
    cW
    tgrpgrp.h
    @2
    eqid
    tgrpgrp.g
    @1
    eqid
    @0
    eqid
    tgrpgrplem
end
