include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "csubmnd.mm"
include "c0g.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cntzssv.mm"
include "a1i.mm"
include "wceq.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantr.mm"
include "simpll.mm"
include "simpr.mm"
include "sselda.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "mndrid.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wb.mm"
include "elcntz.mm"
include "adantl.mm"
include "mpbir2and.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "mndass.mm"
include "syl13anc.mm"
include "cntzi.mm"
include "sylan.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "3eqtrd.mm"
include "ad2antlr.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "issubm.mm"
include "mpbir3and.mm"

theorem cntzsubm
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


  assert |- ( ( M e. Mnd /\ S C_ B ) -> ( Z ` S ) e. ( SubMnd ` M ) )

  proof
    cM
    cmnd
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
    csubmnd
    cfv
    wcel
    #
    @3
    cB
    wss
    #
    cM
    c0g
    cfv
    #
    @3
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vz
    @3
    wral
    vy
    @3
    wral
    #
    @5
    @2
    cB
    cS
    cM
    cZ
    cntzrec.b
    cntzrec.z
    cntzssv
    #
    a1i
    @2
    @7
    @6
    cB
    wcel
    #
    @6
    vx
    cv
    #
    @10
    co
    #
    @16
    @6
    @10
    co
    #
    wceq
    #
    vx
    cS
    wral
    #
    @0
    @15
    @1
    cB
    cM
    @6
    cntzrec.b
    @6
    eqid
    #
    mndidcl
    adantr
    @2
    @19
    vx
    cS
    @2
    @16
    cS
    wcel
    #
    wa
    #
    @17
    @16
    @18
    @23
    @0
    @16
    cB
    wcel
    #
    @17
    @16
    wceq
    @0
    @1
    @22
    simpll
    #
    @2
    cS
    cB
    @16
    @0
    @1
    simpr
    sselda
    #
    cB
    @10
    cM
    @16
    @6
    cntzrec.b
    @10
    eqid
    #
    @21
    mndlid
    syl2anc
    @23
    @0
    @24
    @18
    @16
    wceq
    @25
    @26
    cB
    @10
    cM
    @16
    @6
    cntzrec.b
    @27
    @21
    mndrid
    syl2anc
    eqtr4d
    ralrimiva
    @1
    @7
    @15
    @20
    wa
    wb
    @0
    vx
    @6
    cB
    @10
    cS
    cM
    cZ
    cntzrec.b
    @27
    cntzrec.z
    elcntz
    adantl
    mpbir2and
    @2
    @12
    vy
    vz
    @3
    @3
    @2
    @8
    @3
    wcel
    #
    @9
    @3
    wcel
    #
    wa
    #
    wa
    #
    @12
    @11
    cB
    wcel
    #
    @11
    @16
    @10
    co
    #
    @16
    @11
    @10
    co
    #
    wceq
    #
    vx
    cS
    wral
    #
    @31
    @0
    @8
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @32
    @0
    @1
    @30
    simpll
    #
    @31
    @3
    cB
    @8
    @14
    @2
    @28
    @29
    simprl
    #
    sseldi
    #
    @31
    @3
    cB
    @9
    @14
    @2
    @28
    @29
    simprr
    #
    sseldi
    #
    cB
    @10
    cM
    @8
    @9
    cntzrec.b
    @27
    mndcl
    syl3anc
    @31
    @35
    vx
    cS
    @31
    @22
    wa
    #
    @33
    @8
    @9
    @16
    @10
    co
    #
    @10
    co
    #
    @16
    @8
    @10
    co
    #
    @9
    @10
    co
    #
    @34
    @44
    @0
    @37
    @38
    @24
    @33
    @46
    wceq
    @31
    @0
    @22
    @39
    adantr
    #
    @31
    @37
    @22
    @41
    adantr
    #
    @31
    @38
    @22
    @43
    adantr
    #
    @2
    @22
    @24
    @30
    @26
    adantlr
    #
    cB
    @10
    cM
    @8
    @9
    @16
    cntzrec.b
    @27
    mndass
    syl13anc
    @44
    @46
    @8
    @16
    @9
    @10
    co
    #
    @10
    co
    #
    @8
    @16
    @10
    co
    #
    @9
    @10
    co
    #
    @48
    @44
    @45
    @53
    @8
    @10
    @31
    @29
    @22
    @45
    @53
    wceq
    @42
    @10
    cS
    cM
    @9
    @16
    cZ
    @27
    cntzrec.z
    cntzi
    sylan
    oveq2d
    @44
    @0
    @37
    @24
    @38
    @56
    @54
    wceq
    @49
    @50
    @52
    @51
    cB
    @10
    cM
    @8
    @16
    @9
    cntzrec.b
    @27
    mndass
    syl13anc
    @44
    @55
    @47
    @9
    @10
    @31
    @28
    @22
    @55
    @47
    wceq
    @40
    @10
    cS
    cM
    @8
    @16
    cZ
    @27
    cntzrec.z
    cntzi
    sylan
    oveq1d
    3eqtr2d
    @44
    @0
    @24
    @37
    @38
    @48
    @34
    wceq
    @49
    @52
    @50
    @51
    cB
    @10
    cM
    @16
    @8
    @9
    cntzrec.b
    @27
    mndass
    syl13anc
    3eqtrd
    ralrimiva
    @1
    @12
    @32
    @36
    wa
    wb
    @0
    @30
    vx
    @11
    cB
    @10
    cS
    cM
    cZ
    cntzrec.b
    @27
    cntzrec.z
    elcntz
    ad2antlr
    mpbir2and
    ralrimivva
    @0
    @4
    @5
    @7
    @13
    w3a
    wb
    @1
    vy
    vz
    cB
    @10
    @3
    cM
    @6
    cntzrec.b
    @21
    @27
    issubm
    adantr
    mpbir3and
end
