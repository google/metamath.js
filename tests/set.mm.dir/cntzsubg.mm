include "cgrp.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "csubg.mm"
include "csubmnd.mm"
include "cv.mm"
include "cminusg.mm"
include "wral.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "cntzsubm.mm"
include "sylan.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "simpll.mm"
include "cntzssv.mm"
include "simprl.mm"
include "sseldi.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ssel2.mm"
include "ad2ant2l.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "grpass.mm"
include "syl13anc.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "cntzi.mm"
include "adantl.mm"
include "oveq1d.mm"
include "c0g.mm"
include "grprinv.mm"
include "grprid.mm"
include "eqtrd.mm"
include "grplinv.mm"
include "grplid.mm"
include "3eqtr3d.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simplr.mm"
include "simpr.mm"
include "cntzel.mm"
include "mpbird.mm"
include "issubg3.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem cntzsubg
  let cB: class B
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  assume cntzrec.b: |- B = ( Base ` M )
  assume cntzrec.z: |- Z = ( Cntz ` M )


  assert |- ( ( M e. Grp /\ S C_ B ) -> ( Z ` S ) e. ( SubGrp ` M ) )

  proof
    cM
    cgrp
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cZ
    cfv
    #
    cM
    csubg
    cfv
    wcel
    #
    @3
    cM
    csubmnd
    cfv
    wcel
    #
    vx
    cv
    #
    cM
    cminusg
    cfv
    #
    cfv
    #
    @3
    wcel
    #
    vx
    @3
    wral
    #
    @0
    cM
    cmnd
    wcel
    @1
    @5
    cM
    grpmnd
    cB
    cS
    cM
    cZ
    cntzrec.b
    cntzrec.z
    cntzsubm
    sylan
    @2
    @9
    vx
    @3
    @2
    @6
    @3
    wcel
    #
    wa
    #
    @9
    @8
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @13
    @8
    @14
    co
    #
    wceq
    #
    vy
    cS
    wral
    #
    @12
    @17
    vy
    cS
    @2
    @11
    @13
    cS
    wcel
    #
    @17
    @2
    @11
    @19
    wa
    #
    wa
    #
    @15
    @6
    @8
    @14
    co
    #
    @14
    co
    #
    @8
    @6
    @14
    co
    #
    @16
    @14
    co
    #
    @15
    @16
    @21
    @23
    @8
    @6
    @13
    @14
    co
    #
    @8
    @14
    co
    #
    @14
    co
    #
    @25
    @21
    @23
    @8
    @13
    @6
    @14
    co
    #
    @8
    @14
    co
    #
    @14
    co
    #
    @28
    @21
    @23
    @8
    @13
    @22
    @14
    co
    #
    @14
    co
    #
    @31
    @21
    @0
    @8
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    @23
    @33
    wceq
    @0
    @1
    @20
    simpll
    #
    @21
    @0
    @6
    cB
    wcel
    #
    @34
    @37
    @21
    @3
    cB
    @6
    cB
    cS
    cM
    cZ
    cntzrec.b
    cntzrec.z
    cntzssv
    #
    @2
    @11
    @19
    simprl
    sseldi
    #
    cB
    cM
    @7
    @6
    cntzrec.b
    @7
    eqid
    #
    grpinvcl
    #
    syl2anc
    #
    @1
    @19
    @35
    @0
    @11
    cS
    cB
    @13
    ssel2
    ad2ant2l
    #
    @21
    @0
    @38
    @34
    @36
    @37
    @40
    @43
    cB
    @14
    cM
    @6
    @8
    cntzrec.b
    @14
    eqid
    #
    grpcl
    syl3anc
    cB
    @14
    cM
    @8
    @13
    @22
    cntzrec.b
    @45
    grpass
    syl13anc
    @21
    @30
    @32
    @8
    @14
    @21
    @0
    @35
    @38
    @34
    @30
    @32
    wceq
    @37
    @44
    @40
    @43
    cB
    @14
    cM
    @13
    @6
    @8
    cntzrec.b
    @45
    grpass
    syl13anc
    oveq2d
    eqtr4d
    @21
    @27
    @30
    @8
    @14
    @21
    @26
    @29
    @8
    @14
    @20
    @26
    @29
    wceq
    @2
    @14
    cS
    cM
    @6
    @13
    cZ
    @45
    cntzrec.z
    cntzi
    adantl
    oveq1d
    oveq2d
    eqtr4d
    @21
    @25
    @8
    @6
    @16
    @14
    co
    #
    @14
    co
    #
    @28
    @21
    @0
    @34
    @38
    @16
    cB
    wcel
    #
    @25
    @47
    wceq
    @37
    @43
    @40
    @21
    @0
    @35
    @34
    @48
    @37
    @44
    @43
    cB
    @14
    cM
    @13
    @8
    cntzrec.b
    @45
    grpcl
    syl3anc
    #
    cB
    @14
    cM
    @8
    @6
    @16
    cntzrec.b
    @45
    grpass
    syl13anc
    @21
    @27
    @46
    @8
    @14
    @21
    @0
    @38
    @35
    @34
    @27
    @46
    wceq
    @37
    @40
    @44
    @43
    cB
    @14
    cM
    @6
    @13
    @8
    cntzrec.b
    @45
    grpass
    syl13anc
    oveq2d
    eqtr4d
    eqtr4d
    @21
    @23
    @15
    cM
    c0g
    cfv
    #
    @14
    co
    #
    @15
    @21
    @22
    @50
    @15
    @14
    @21
    @0
    @38
    @22
    @50
    wceq
    @37
    @40
    cB
    @14
    cM
    @7
    @6
    @50
    cntzrec.b
    @45
    @50
    eqid
    #
    @41
    grprinv
    syl2anc
    oveq2d
    @21
    @0
    @15
    cB
    wcel
    #
    @51
    @15
    wceq
    @37
    @21
    @0
    @34
    @35
    @53
    @37
    @43
    @44
    cB
    @14
    cM
    @8
    @13
    cntzrec.b
    @45
    grpcl
    syl3anc
    cB
    @14
    cM
    @15
    @50
    cntzrec.b
    @45
    @52
    grprid
    syl2anc
    eqtrd
    @21
    @25
    @50
    @16
    @14
    co
    #
    @16
    @21
    @24
    @50
    @16
    @14
    @21
    @0
    @38
    @24
    @50
    wceq
    @37
    @40
    cB
    @14
    cM
    @7
    @6
    @50
    cntzrec.b
    @45
    @52
    @41
    grplinv
    syl2anc
    oveq1d
    @21
    @0
    @48
    @54
    @16
    wceq
    @37
    @49
    cB
    @14
    cM
    @16
    @50
    cntzrec.b
    @45
    @52
    grplid
    syl2anc
    eqtrd
    3eqtr3d
    anassrs
    ralrimiva
    @12
    @1
    @34
    @9
    @18
    wb
    @0
    @1
    @11
    simplr
    @12
    @0
    @38
    @34
    @0
    @1
    @11
    simpll
    @12
    @3
    cB
    @6
    @39
    @2
    @11
    simpr
    sseldi
    @42
    syl2anc
    vy
    cB
    @14
    cS
    cM
    @8
    cZ
    cntzrec.b
    @45
    cntzrec.z
    cntzel
    syl2anc
    mpbird
    ralrimiva
    @0
    @4
    @5
    @10
    wa
    wb
    @1
    vx
    @3
    cM
    @7
    @41
    issubg3
    adantr
    mpbir2and
end
