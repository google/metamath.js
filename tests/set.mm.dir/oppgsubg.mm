include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "oppggrpb.mm"
include "sylibr.mm"
include "csubmnd.mm"
include "cminusg.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "oppgsubm.mm"
include "eleq2i.mm"
include "a1i.mm"
include "eqid.mm"
include "oppginv.mm"
include "fveq1d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "issubg3.mm"
include "sylbi.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"
include "eqriv.mm"

theorem oppgsubg
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cZ: class Z
  assume oppggic.o: |- O = ( oppG ` G )


  assert |- ( SubGrp ` G ) = ( SubGrp ` O )

  proof
    vx
    cG
    csubg
    cfv
    #
    cO
    csubg
    cfv
    #
    vx
    cv
    #
    @0
    wcel
    #
    cG
    cgrp
    wcel
    #
    @2
    @1
    wcel
    #
    @2
    cG
    subgrcl
    @5
    cO
    cgrp
    wcel
    #
    @4
    @2
    cO
    subgrcl
    cG
    cO
    oppggic.o
    oppggrpb
    #
    sylibr
    @4
    @2
    cG
    csubmnd
    cfv
    #
    wcel
    #
    vy
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    @2
    wcel
    #
    vy
    @2
    wral
    #
    wa
    @2
    cO
    csubmnd
    cfv
    #
    wcel
    #
    @10
    cO
    cminusg
    cfv
    #
    cfv
    #
    @2
    wcel
    #
    vy
    @2
    wral
    #
    wa
    #
    @3
    @5
    @4
    @9
    @16
    @14
    @20
    @9
    @16
    wb
    @4
    @8
    @15
    @2
    cG
    cO
    oppggic.o
    oppgsubm
    eleq2i
    a1i
    @4
    @13
    @19
    vy
    @2
    @4
    @12
    @18
    @2
    @4
    @10
    @11
    @17
    cG
    @11
    cO
    oppggic.o
    @11
    eqid
    #
    oppginv
    fveq1d
    eleq1d
    ralbidv
    anbi12d
    vy
    @2
    cG
    @11
    @22
    issubg3
    @4
    @6
    @5
    @21
    wb
    @7
    vy
    @2
    cO
    @17
    @17
    eqid
    issubg3
    sylbi
    3bitr4d
    pm5.21nii
    eqriv
end
