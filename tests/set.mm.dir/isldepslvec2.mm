include "clvec.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "clindeps.mm"
include "clmod.mm"
include "cnzr.mm"
include "wi.mm"
include "lveclmod.mm"
include "adantr.mm"
include "simpr.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "drngnzr.mm"
include "syl.mm"
include "islindeps2.mm"
include "syl3anc.mm"
include "wne.mm"
include "w3a.mm"
include "islindeps.mm"
include "df-3an.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "rexbii.mm"
include "rexcom.mm"
include "bitri.mm"
include "cminusg.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cui.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "3jca.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "anim12i.mm"
include "wb.mm"
include "eqid.mm"
include "drngunit.mm"
include "mpbird.mm"
include "simpll.mm"
include "adantl.mm"
include "lincresunit2.mm"
include "syl13anc.mm"
include "simprr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "lincreslvec3.mm"
include "syl131anc.mm"
include "lincresunit1.mm"
include "syl12anc.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "mp2and.mm"
include "ex.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "impbid.mm"

theorem isldepslvec2
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vg: setvar g
  let vz: setvar z
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume islindeps2.b: |- B = ( Base ` M )
  assume islindeps2.z: |- Z = ( 0g ` M )
  assume islindeps2.r: |- R = ( Scalar ` M )
  assume islindeps2.e: |- E = ( Base ` R )
  assume islindeps2.0: |- .0. = ( 0g ` R )

  disjoint B f
  disjoint B s
  disjoint f s
  disjoint E f
  disjoint E s
  disjoint M f
  disjoint M s
  disjoint R f
  disjoint R s
  disjoint S f
  disjoint S s
  disjoint Z f
  disjoint Z s
  disjoint .0. f
  disjoint .0. s
  disjoint B g
  disjoint B z
  disjoint f g
  disjoint f z
  disjoint g s
  disjoint g z
  disjoint s z
  disjoint E g
  disjoint E z
  disjoint M g
  disjoint M z
  disjoint R g
  disjoint R z
  disjoint S g
  disjoint S z
  disjoint Z g
  disjoint .0. g
  disjoint B y
  disjoint s y
  disjoint g y
  disjoint E y
  disjoint M y
  disjoint R y
  disjoint S y
  disjoint Z y
  disjoint Z z
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint k x
  assert |- ( ( M e. LVec /\ S e. ~P B ) -> ( E. s e. S E. f e. ( E ^m ( S \ { s } ) ) ( f finSupp .0. /\ ( f ( linC ` M ) ( S \ { s } ) ) = s ) <-> S linDepS M ) )

  proof
    cM
    clvec
    wcel
    #
    cS
    cB
    cpw
    wcel
    #
    wa
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @3
    cS
    vs
    cv
    #
    csn
    cdif
    #
    cM
    clinc
    cfv
    #
    co
    #
    @5
    wceq
    #
    wa
    #
    vf
    cE
    @6
    cmap
    co
    #
    wrex
    #
    vs
    cS
    wrex
    #
    cS
    cM
    clindeps
    wbr
    #
    @2
    cM
    clmod
    wcel
    #
    @1
    cR
    cnzr
    wcel
    #
    @13
    @14
    wi
    @0
    @15
    @1
    cM
    lveclmod
    #
    adantr
    @0
    @1
    simpr
    @0
    @16
    @1
    @0
    cR
    cdr
    wcel
    #
    @16
    cR
    cM
    islindeps2.r
    lvecdrng
    #
    cR
    drngnzr
    syl
    adantr
    cB
    cR
    cS
    vf
    cE
    cM
    c.0
    cZ
    vs
    islindeps2.b
    islindeps2.z
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps2
    syl3anc
    @2
    @14
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @20
    cS
    @7
    co
    cZ
    wceq
    #
    @5
    @20
    cfv
    #
    c.0
    wne
    #
    vs
    cS
    wrex
    #
    w3a
    #
    vg
    cE
    cS
    cmap
    co
    #
    wrex
    #
    @13
    vs
    cB
    cR
    cS
    vg
    cE
    cM
    clvec
    c.0
    cZ
    islindeps2.b
    islindeps2.z
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps
    @28
    @21
    @22
    wa
    #
    @24
    wa
    #
    vg
    @27
    wrex
    #
    vs
    cS
    wrex
    #
    @2
    @13
    @28
    @30
    vs
    cS
    wrex
    #
    vg
    @27
    wrex
    @32
    @26
    @33
    vg
    @27
    @26
    @29
    @25
    wa
    @33
    @21
    @22
    @25
    df-3an
    @29
    @24
    vs
    cS
    r19.42v
    bitr4i
    rexbii
    @30
    vg
    vs
    @27
    cS
    rexcom
    bitri
    @2
    @31
    @12
    vs
    cS
    @2
    @5
    cS
    wcel
    #
    wa
    #
    @30
    @12
    vg
    @27
    @35
    @20
    @27
    wcel
    #
    wa
    #
    @30
    @12
    @37
    @30
    wa
    #
    vz
    @6
    @23
    cR
    cminusg
    cfv
    #
    cfv
    cR
    cinvr
    cfv
    #
    cfv
    #
    vz
    cv
    #
    @20
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    c.0
    cfsupp
    wbr
    #
    @46
    @6
    @7
    co
    #
    @5
    wceq
    #
    @12
    @38
    @1
    @15
    @34
    w3a
    #
    @36
    @23
    cR
    cui
    cfv
    #
    wcel
    #
    @21
    @47
    @35
    @50
    @36
    @30
    @35
    @1
    @15
    @34
    @0
    @1
    @34
    simplr
    #
    @0
    @15
    @1
    @34
    @17
    ad2antrr
    @2
    @34
    simpr
    #
    3jca
    ad2antrr
    #
    @35
    @36
    @30
    simplr
    #
    @38
    @52
    @23
    cE
    wcel
    #
    @24
    wa
    #
    @37
    @57
    @30
    @24
    @36
    cS
    cE
    @20
    wf
    @34
    @57
    @35
    @20
    cE
    cS
    elmapi
    @54
    cS
    cE
    @5
    @20
    ffvelrn
    syl2anr
    @29
    @24
    simpr
    anim12i
    @38
    @18
    @52
    @58
    wb
    @35
    @18
    @36
    @30
    @0
    @18
    @1
    @34
    @19
    ad2antrr
    ad2antrr
    cE
    cR
    @51
    @23
    c.0
    islindeps2.e
    @51
    eqid
    #
    islindeps2.0
    drngunit
    syl
    mpbird
    #
    @30
    @21
    @37
    @21
    @22
    @24
    simpll
    adantl
    #
    cB
    cR
    cS
    @44
    @51
    cE
    @20
    @46
    @40
    cM
    @39
    @5
    c.0
    cZ
    vz
    islindeps2.b
    islindeps2.r
    islindeps2.e
    @59
    islindeps2.0
    islindeps2.z
    @39
    eqid
    #
    @40
    eqid
    #
    @44
    eqid
    #
    @46
    eqid
    #
    lincresunit2
    syl13anc
    @38
    @1
    @0
    @34
    w3a
    #
    @36
    @24
    @21
    @22
    @49
    @35
    @66
    @36
    @30
    @35
    @1
    @0
    @34
    @53
    @0
    @1
    @34
    simpll
    @54
    3jca
    ad2antrr
    @56
    @37
    @29
    @24
    simprr
    @61
    @30
    @22
    @37
    @21
    @22
    @24
    simplr
    adantl
    cB
    cR
    cS
    @44
    @51
    cE
    @20
    @46
    @40
    cM
    @39
    @5
    c.0
    cZ
    vy
    islindeps2.b
    islindeps2.r
    islindeps2.e
    @59
    islindeps2.0
    islindeps2.z
    @62
    @63
    @64
    vz
    vy
    @6
    @45
    @41
    vy
    cv
    #
    @20
    cfv
    #
    @44
    co
    @42
    @67
    wceq
    @43
    @68
    @41
    @44
    @42
    @67
    @20
    fveq2
    oveq2d
    cbvmptv
    lincreslvec3
    syl131anc
    @38
    @10
    @47
    @49
    wa
    #
    vf
    @46
    @11
    @38
    @50
    @36
    @52
    @46
    @11
    wcel
    @55
    @56
    @60
    cB
    cR
    cS
    @44
    @51
    cE
    @20
    @46
    @40
    cM
    @39
    @5
    c.0
    cZ
    vz
    islindeps2.b
    islindeps2.r
    islindeps2.e
    @59
    islindeps2.0
    islindeps2.z
    @62
    @63
    @64
    @65
    lincresunit1
    syl12anc
    @3
    @46
    wceq
    #
    @10
    @69
    wb
    @38
    @70
    @4
    @47
    @9
    @49
    @3
    @46
    c.0
    cfsupp
    breq1
    @70
    @8
    @48
    @5
    @3
    @46
    @6
    @7
    oveq1
    eqeq1d
    anbi12d
    adantl
    rspcedv
    mp2and
    ex
    rexlimdva
    reximdva
    syl5bi
    sylbid
    impbid
end
