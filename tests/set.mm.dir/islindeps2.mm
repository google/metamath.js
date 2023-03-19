include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "cnzr.mm"
include "w3a.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csn.mm"
include "cdif.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "clindeps.mm"
include "wne.mm"
include "cur.mm"
include "cminusg.mm"
include "cif.mm"
include "cmpt.mm"
include "id.mm"
include "3adant3.mm"
include "ad3antrrr.mm"
include "crg.mm"
include "nzrring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "simpllr.mm"
include "simplr.mm"
include "3jca.mm"
include "simprl.mm"
include "lincext2.mm"
include "syl3anc.mm"
include "cvsca.mm"
include "simpl1.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqcomd.mm"
include "adantl.mm"
include "sylan9eq.mm"
include "lincext3.mm"
include "syl112anc.mm"
include "jca.mm"
include "cvv.mm"
include "eqidd.mm"
include "iftrue.mm"
include "simpr.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "c0g.mm"
include "nzrneg1ne0.mm"
include "a1i.mm"
include "neeqtrrd.mm"
include "eqnetrd.mm"
include "lincext1.mm"
include "wb.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "rspcedv.mm"
include "mp2and.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "reximdva.mm"
include "df-3an.mm"
include "r19.42v.mm"
include "bitr4i.mm"
include "rexbii.mm"
include "rexcom.mm"
include "bitri.mm"
include "sylibr.mm"
include "islindeps.mm"
include "mpbird.mm"
include "ex.mm"

theorem islindeps2
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
  disjoint k x
  assert |- ( ( M e. LMod /\ S e. ~P B /\ R e. NzRing ) -> ( E. s e. S E. f e. ( E ^m ( S \ { s } ) ) ( f finSupp .0. /\ ( f ( linC ` M ) ( S \ { s } ) ) = s ) -> S linDepS M ) )

  proof
    cM
    clmod
    wcel
    #
    cS
    cB
    cpw
    wcel
    #
    cR
    cnzr
    wcel
    #
    w3a
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @4
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
    @6
    wceq
    #
    wa
    #
    vf
    cE
    @7
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
    @3
    @14
    wa
    #
    @15
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @17
    cS
    @8
    co
    #
    cZ
    wceq
    #
    @6
    @17
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
    @16
    @18
    @20
    wa
    #
    @22
    wa
    #
    vg
    @25
    wrex
    #
    vs
    cS
    wrex
    #
    @26
    @3
    @14
    @30
    @3
    @13
    @29
    vs
    cS
    @3
    @6
    cS
    wcel
    #
    wa
    #
    @11
    @29
    vf
    @12
    @32
    @4
    @12
    wcel
    #
    @11
    @29
    @32
    @33
    wa
    #
    @11
    wa
    #
    vz
    cS
    vz
    cv
    #
    @6
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    @36
    @4
    cfv
    #
    cif
    #
    cmpt
    #
    c.0
    cfsupp
    wbr
    #
    @43
    cS
    @8
    co
    #
    cZ
    wceq
    #
    wa
    #
    @6
    @43
    cfv
    #
    c.0
    wne
    #
    @29
    @35
    @44
    @46
    @35
    @0
    @1
    wa
    #
    @38
    cE
    wcel
    #
    @31
    @33
    w3a
    #
    @5
    @44
    @3
    @50
    @31
    @33
    @11
    @0
    @1
    @50
    @2
    @50
    id
    3adant3
    ad3antrrr
    #
    @35
    @51
    @31
    @33
    @3
    @51
    @31
    @33
    @11
    @2
    @0
    @51
    @1
    @2
    cR
    crg
    wcel
    @51
    cR
    nzrring
    cE
    cR
    @38
    islindeps2.e
    @38
    eqid
    #
    ringidcl
    syl
    3ad2ant3
    ad3antrrr
    @3
    @31
    @33
    @11
    simpllr
    @32
    @33
    @11
    simplr
    3jca
    #
    @34
    @5
    @10
    simprl
    #
    vz
    cB
    cR
    cS
    cE
    @43
    @4
    cM
    @39
    @6
    @38
    c.0
    cZ
    islindeps2.b
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps2.z
    @39
    eqid
    #
    @43
    eqid
    #
    lincext2
    syl3anc
    @35
    @50
    @52
    @5
    @38
    @6
    cM
    cvsca
    cfv
    #
    co
    #
    @9
    wceq
    @46
    @53
    @55
    @56
    @34
    @11
    @60
    @6
    @9
    @32
    @60
    @6
    wceq
    #
    @33
    @32
    @0
    @6
    cB
    wcel
    #
    @61
    @0
    @1
    @2
    @31
    simpl1
    @3
    @31
    @62
    @1
    @0
    @31
    @62
    wi
    @2
    @31
    @1
    @62
    @6
    cS
    cB
    elelpwi
    expcom
    3ad2ant2
    imp
    @59
    @38
    cR
    cB
    cM
    @6
    islindeps2.b
    islindeps2.r
    @59
    eqid
    @54
    lmodvs1
    syl2anc
    adantr
    @10
    @6
    @9
    wceq
    @5
    @10
    @9
    @6
    @10
    id
    eqcomd
    adantl
    sylan9eq
    vz
    cB
    cR
    cS
    cE
    @43
    @4
    cM
    @39
    @6
    @38
    c.0
    cZ
    islindeps2.b
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps2.z
    @57
    @58
    lincext3
    syl112anc
    jca
    @34
    @49
    @11
    @32
    @49
    @33
    @32
    @48
    @40
    c.0
    @32
    vz
    @6
    @42
    @40
    cS
    @43
    cvv
    @32
    @43
    eqidd
    @37
    @42
    @40
    wceq
    @32
    @37
    @40
    @41
    iftrue
    adantl
    @3
    @31
    simpr
    @32
    @38
    @39
    fvexd
    fvmptd
    @3
    @40
    c.0
    wne
    #
    @31
    @2
    @0
    @63
    @1
    @2
    @40
    cR
    c0g
    cfv
    #
    c.0
    cR
    nzrneg1ne0
    c.0
    @64
    wceq
    @2
    islindeps2.0
    a1i
    neeqtrrd
    3ad2ant3
    adantr
    eqnetrd
    adantr
    adantr
    @35
    @28
    @47
    @49
    wa
    #
    vg
    @43
    @25
    @35
    @50
    @52
    @43
    @25
    wcel
    @53
    @55
    vz
    cB
    cR
    cS
    cE
    @43
    @4
    cM
    @39
    @6
    @38
    c.0
    cZ
    islindeps2.b
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps2.z
    @57
    @58
    lincext1
    syl2anc
    @17
    @43
    wceq
    #
    @28
    @65
    wb
    @35
    @66
    @27
    @47
    @22
    @49
    @66
    @18
    @44
    @20
    @46
    @17
    @43
    c.0
    cfsupp
    breq1
    @66
    @19
    @45
    cZ
    @17
    @43
    cS
    @8
    oveq1
    eqeq1d
    anbi12d
    @66
    @21
    @48
    c.0
    @6
    @17
    @43
    fveq1
    neeq1d
    anbi12d
    adantl
    rspcedv
    mp2and
    exp31
    rexlimdv
    reximdva
    imp
    @26
    @28
    vs
    cS
    wrex
    #
    vg
    @25
    wrex
    @30
    @24
    @67
    vg
    @25
    @24
    @27
    @23
    wa
    @67
    @18
    @20
    @23
    df-3an
    @27
    @22
    vs
    cS
    r19.42v
    bitr4i
    rexbii
    @28
    vg
    vs
    @25
    cS
    rexcom
    bitri
    sylibr
    @3
    @15
    @26
    wb
    #
    @14
    @0
    @1
    @68
    @2
    vs
    cB
    cR
    cS
    vg
    cE
    cM
    clmod
    c.0
    cZ
    islindeps2.b
    islindeps2.z
    islindeps2.r
    islindeps2.e
    islindeps2.0
    islindeps
    3adant3
    adantr
    mpbird
    ex
end
