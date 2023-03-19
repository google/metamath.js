include "cpreset.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isprs.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "vex.mm"
include "brcnv.mm"
include "sylibr.mm"
include "simprd.mm"
include "an32s.mm"
include "ex.mm"
include "imp.mm"
include "anbi12ci.mm"
include "3imtr4g.mm"
include "jca.mm"
include "ralrimiva.mm"
include "codu.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctil.mm"
include "odubas.mm"
include "oduleval.mm"

theorem oduprs
  let cD: class D
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oduprs.d: |- D = ( ODual ` K )


  assert |- ( K e. Preset -> D e. Preset )

  proof
    cK
    cpreset
    wcel
    #
    cD
    cvv
    wcel
    #
    vx
    cv
    #
    @2
    cK
    cple
    cfv
    #
    ccnv
    #
    wbr
    #
    @2
    vy
    cv
    #
    @4
    wbr
    #
    @6
    vz
    cv
    #
    @4
    wbr
    #
    wa
    #
    @2
    @8
    @4
    wbr
    #
    wi
    #
    wa
    #
    vz
    cK
    cbs
    cfv
    #
    wral
    #
    vy
    @14
    wral
    #
    vx
    @14
    wral
    #
    wa
    cD
    cpreset
    wcel
    @0
    @17
    @1
    @0
    @16
    vx
    @14
    @0
    @2
    @14
    wcel
    #
    wa
    #
    @15
    vy
    @14
    @19
    @6
    @14
    wcel
    #
    wa
    #
    @13
    vz
    @14
    @21
    @8
    @14
    wcel
    #
    wa
    #
    @5
    @12
    @23
    @2
    @2
    @3
    wbr
    #
    @5
    @23
    @24
    @2
    @6
    @3
    wbr
    @6
    @8
    @3
    wbr
    wa
    @2
    @8
    @3
    wbr
    wi
    #
    @21
    @24
    @25
    wa
    #
    vz
    @14
    @19
    @26
    vz
    @14
    wral
    #
    vy
    @14
    @0
    @27
    vy
    @14
    wral
    #
    vx
    @14
    @0
    cK
    cvv
    wcel
    #
    @28
    vx
    @14
    wral
    vx
    vy
    vz
    @14
    cK
    @3
    @14
    eqid
    #
    @3
    eqid
    #
    isprs
    simprbi
    r19.21bi
    r19.21bi
    r19.21bi
    simpld
    @2
    @2
    @3
    vx
    vex
    #
    @32
    brcnv
    sylibr
    @23
    @8
    @6
    @3
    wbr
    #
    @6
    @2
    @3
    wbr
    #
    wa
    #
    @8
    @2
    @3
    wbr
    #
    @10
    @11
    @19
    @22
    @20
    @35
    @36
    wi
    #
    @19
    @22
    wa
    @20
    @37
    @0
    @22
    @18
    @20
    @37
    wi
    @0
    @22
    wa
    #
    @18
    wa
    @20
    @37
    @38
    @20
    @18
    @37
    @38
    @20
    wa
    #
    @18
    wa
    @8
    @8
    @3
    wbr
    #
    @37
    @39
    @40
    @37
    wa
    #
    vx
    @14
    @38
    @41
    vx
    @14
    wral
    #
    vy
    @14
    @0
    @42
    vy
    @14
    wral
    #
    vz
    @14
    @0
    @29
    @43
    vz
    @14
    wral
    vz
    vy
    vx
    @14
    cK
    @3
    @30
    @31
    isprs
    simprbi
    r19.21bi
    r19.21bi
    r19.21bi
    simprd
    an32s
    ex
    an32s
    imp
    an32s
    @7
    @34
    @9
    @33
    @2
    @6
    @3
    @32
    vy
    vex
    #
    brcnv
    @6
    @8
    @3
    @44
    vz
    vex
    #
    brcnv
    anbi12ci
    @2
    @8
    @3
    @32
    @45
    brcnv
    3imtr4g
    jca
    ralrimiva
    ralrimiva
    ralrimiva
    cD
    cK
    codu
    cfv
    cvv
    oduprs.d
    cK
    codu
    fvex
    eqeltri
    jctil
    vx
    vy
    vz
    @14
    cD
    @4
    @14
    cD
    cK
    oduprs.d
    @30
    odubas
    cD
    @3
    cK
    oduprs.d
    @31
    oduleval
    isprs
    sylibr
end
