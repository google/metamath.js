include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cltrn.mm"
include "cfv.mm"
include "cplusg.mm"
include "cbs.mm"
include "eqid.mm"
include "tgrpbase.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "tgrpgrp.mm"
include "cv.mm"
include "w3a.mm"
include "ccom.mm"
include "co.mm"
include "ltrncom.mm"
include "wceq.mm"
include "tgrpov.mm"
include "3expa.mm"
include "3impb.mm"
include "3com23.mm"
include "3eqtr4d.mm"
include "isabld.mm"

theorem tgrpabl
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume tgrpgrp.h: |- H = ( LHyp ` K )
  assume tgrpgrp.g: |- G = ( ( TGrp ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> G e. Abel )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    vf
    vg
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cG
    cplusg
    cfv
    #
    cG
    @2
    cG
    cbs
    cfv
    #
    @3
    @5
    @3
    cG
    cH
    cK
    chlt
    cW
    tgrpgrp.h
    @3
    eqid
    #
    tgrpgrp.g
    @5
    eqid
    tgrpbase
    eqcomd
    @2
    @4
    eqidd
    cG
    cH
    cK
    cW
    tgrpgrp.h
    tgrpgrp.g
    tgrpgrp
    @2
    vf
    cv
    #
    @3
    wcel
    #
    vg
    cv
    #
    @3
    wcel
    #
    w3a
    @7
    @9
    ccom
    #
    @9
    @7
    ccom
    #
    @7
    @9
    @4
    co
    #
    @9
    @7
    @4
    co
    #
    @3
    @7
    @9
    cH
    cK
    cW
    tgrpgrp.h
    @6
    ltrncom
    @2
    @8
    @10
    @13
    @11
    wceq
    #
    @0
    @1
    @8
    @10
    wa
    @15
    @4
    @3
    cG
    cH
    cK
    chlt
    cW
    @7
    @9
    tgrpgrp.h
    @6
    tgrpgrp.g
    @4
    eqid
    #
    tgrpov
    3expa
    3impb
    @2
    @10
    @8
    @14
    @12
    wceq
    #
    @2
    @10
    @8
    @17
    @0
    @1
    @10
    @8
    wa
    @17
    @4
    @3
    cG
    cH
    cK
    chlt
    cW
    @9
    @7
    tgrpgrp.h
    @6
    tgrpgrp.g
    @16
    tgrpov
    3expa
    3impb
    3com23
    3eqtr4d
    isabld
end
