include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wne.mm"
include "cltrn.mm"
include "cmpt.mm"
include "cop.mm"
include "csn.mm"
include "clspn.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "dih1dimb2.mm"
include "anassrs.mm"
include "w3a.mm"
include "simp3rr.mm"
include "clmod.mm"
include "c0g.mm"
include "simp1l.mm"
include "dvhlmod.mm"
include "ctendo.mm"
include "simp3l.mm"
include "tendo0cl.mm"
include "syl.mm"
include "dvhelvbasei.mm"
include "syl12anc.mm"
include "wn.mm"
include "simp3rl.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "vex.mm"
include "fvex.mm"
include "mptex.mm"
include "opth.mm"
include "necon3abii.mm"
include "sylibr.mm"
include "dvh0g.mm"
include "neeqtrrd.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "3expa.mm"
include "rexlimddv.mm"
include "coc.mm"
include "crio.mm"
include "dih1dimc.mm"
include "simpll.mm"
include "lhpocnel.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "ltrniotacl.mm"
include "syl112anc.mm"
include "tendoidcl.mm"
include "tendo1ne0.mm"
include "intnand.mm"
include "riotaex.mm"
include "cvv.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "pm2.61dan.mm"

theorem dihatlat
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume dihatlat.a: |- A = ( Atoms ` K )
  assume dihatlat.h: |- H = ( LHyp ` K )
  assume dihatlat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihatlat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihatlat.l: |- L = ( LSAtoms ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ Q e. A ) -> ( I ` Q ) e. L )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cQ
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    cQ
    cI
    cfv
    #
    cL
    wcel
    #
    @2
    @4
    wa
    vg
    cv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    wne
    #
    @5
    @7
    vf
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    @9
    cmpt
    #
    cop
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    @6
    vg
    @12
    @0
    @1
    @4
    @18
    vg
    @12
    wrex
    cA
    @8
    cQ
    @12
    cU
    vg
    vf
    cH
    cI
    cK
    @3
    @15
    @13
    cW
    @8
    eqid
    #
    @3
    eqid
    #
    dihatlat.a
    dihatlat.h
    @12
    eqid
    #
    @13
    eqid
    #
    dihatlat.u
    dihatlat.i
    @15
    eqid
    #
    dih1dimb2
    anassrs
    @2
    @4
    @7
    @12
    wcel
    #
    @18
    wa
    #
    @6
    @2
    @4
    @25
    w3a
    #
    @5
    @16
    cL
    @10
    @17
    @24
    @2
    @4
    simp3rr
    @26
    cU
    clmod
    wcel
    #
    @14
    cU
    cbs
    cfv
    #
    wcel
    #
    @14
    cU
    c0g
    cfv
    #
    wne
    @16
    cL
    wcel
    @26
    cU
    cH
    cK
    cW
    dihatlat.h
    dihatlat.u
    @0
    @1
    @4
    @25
    simp1l
    #
    dvhlmod
    @26
    @0
    @24
    @13
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @29
    @31
    @2
    @4
    @24
    @18
    simp3l
    @26
    @0
    @33
    @31
    @8
    @12
    vf
    @32
    cH
    cK
    @13
    cW
    @19
    dihatlat.h
    @21
    @32
    eqid
    #
    @22
    tendo0cl
    syl
    @13
    @12
    cU
    @32
    @7
    cH
    cK
    @28
    cW
    chlt
    dihatlat.h
    @21
    @34
    dihatlat.u
    @28
    eqid
    #
    dvhelvbasei
    syl12anc
    @26
    @14
    @9
    @13
    cop
    #
    @30
    @26
    @7
    @9
    wceq
    #
    @13
    @13
    wceq
    #
    wa
    #
    wn
    @14
    @36
    wne
    @26
    @37
    @38
    @26
    @7
    @9
    @10
    @17
    @24
    @2
    @4
    simp3rl
    neneqd
    intnanrd
    @39
    @14
    @36
    @7
    @13
    @9
    @13
    vg
    vex
    vf
    @12
    @9
    cW
    @11
    fvex
    #
    mptex
    opth
    necon3abii
    sylibr
    @26
    @0
    @30
    @36
    wceq
    #
    @31
    @8
    @12
    cU
    vf
    cH
    cK
    @13
    cW
    @30
    @19
    dihatlat.h
    @21
    dihatlat.u
    @30
    eqid
    #
    @22
    dvh0g
    #
    syl
    neeqtrrd
    cL
    @15
    @28
    cU
    @14
    @30
    @35
    @23
    @42
    dihatlat.l
    lsatlspsn2
    syl3anc
    eqeltrd
    3expa
    rexlimddv
    @2
    @4
    wn
    #
    wa
    #
    @5
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vf
    cv
    cfv
    cQ
    wceq
    #
    vf
    @12
    crio
    #
    cid
    @12
    cres
    #
    cop
    #
    csn
    @15
    cfv
    #
    cL
    @0
    @1
    @44
    @5
    @52
    wceq
    cA
    @47
    cQ
    @12
    cU
    vf
    @49
    cH
    cI
    cK
    @3
    @15
    cW
    @20
    dihatlat.a
    dihatlat.h
    @47
    eqid
    @21
    dihatlat.i
    dihatlat.u
    @23
    @49
    eqid
    #
    dih1dimc
    anassrs
    @45
    @27
    @51
    @28
    wcel
    #
    @51
    @30
    wne
    @52
    cL
    wcel
    @45
    cU
    cH
    cK
    cW
    dihatlat.h
    dihatlat.u
    @0
    @1
    @44
    simpll
    #
    dvhlmod
    @45
    @0
    @49
    @12
    wcel
    #
    @50
    @32
    wcel
    #
    @54
    @55
    @45
    @0
    @47
    cA
    wcel
    @47
    cW
    @3
    wbr
    wn
    wa
    #
    @1
    @44
    @56
    @55
    @0
    @58
    @1
    @44
    cA
    cH
    cK
    @3
    @46
    cW
    @20
    @46
    eqid
    dihatlat.a
    dihatlat.h
    lhpocnel
    ad2antrr
    @0
    @1
    @44
    simplr
    @2
    @44
    simpr
    cA
    @47
    cQ
    @12
    vf
    @49
    cH
    cK
    @3
    cW
    @20
    dihatlat.a
    dihatlat.h
    @21
    @53
    ltrniotacl
    syl112anc
    @0
    @57
    @1
    @44
    @12
    @32
    cH
    cK
    cW
    dihatlat.h
    @21
    @34
    tendoidcl
    ad2antrr
    @50
    @12
    cU
    @32
    @49
    cH
    cK
    @28
    cW
    chlt
    dihatlat.h
    @21
    @34
    dihatlat.u
    @35
    dvhelvbasei
    syl12anc
    @45
    @51
    @36
    @30
    @45
    @49
    @9
    wceq
    #
    @50
    @13
    wceq
    #
    wa
    #
    wn
    @51
    @36
    wne
    @45
    @60
    @59
    @45
    @50
    @13
    @0
    @50
    @13
    wne
    @1
    @44
    @8
    @12
    vf
    @32
    cH
    cK
    @13
    cW
    @19
    dihatlat.h
    @21
    @34
    @22
    tendo1ne0
    ad2antrr
    neneqd
    intnand
    @61
    @51
    @36
    @49
    @50
    @9
    @13
    @48
    vf
    @12
    riotaex
    @12
    cvv
    wcel
    @50
    cvv
    wcel
    @40
    @12
    cvv
    resiexg
    ax-mp
    opth
    necon3abii
    sylibr
    @0
    @41
    @1
    @44
    @43
    ad2antrr
    neeqtrrd
    cL
    @15
    @28
    cU
    @51
    @30
    @35
    @23
    @42
    dihatlat.l
    lsatlspsn2
    syl3anc
    eqeltrd
    pm2.61dan
end
