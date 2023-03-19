include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cn.mm"
include "crn.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "fzfid.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cz.mm"
include "wf.mm"
include "wss.mm"
include "mulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "adantlr.mm"
include "fmptd.mm"
include "frn.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "3syl.mm"
include "wral.mm"
include "wreu.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ovex.mm"
include "oveq1.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "ralrimiva.mm"
include "cmo.mm"
include "zmodfz.mm"
include "ancoms.mm"
include "adantll.mm"
include "cdvds.mm"
include "simpllr.mm"
include "simplr.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "clt.mm"
include "zred.mm"
include "nnrpd.mm"
include "w3a.mm"
include "0z.mm"
include "nnz.mm"
include "adantr.mm"
include "elfzm11.mm"
include "sylancr.mm"
include "biimpa.mm"
include "simp2d.mm"
include "simp3d.mm"
include "modid.mm"
include "syl22anc.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "c0g.mm"
include "eqid.mm"
include "odcong.mm"
include "syl112anc.mm"
include "3bitr3rd.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "rgenw.mm"
include "eqeq1.mm"
include "reubidv.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "f1ompt.mm"
include "sylanbrc.mm"
include "f1oen2g.mm"
include "enfi.mm"
include "syl.mm"
include "mpbid.mm"
include "iftrued.mm"
include "fz01en.mm"
include "ensym.mm"
include "entr.mm"
include "hashen.mm"
include "mpbird.mm"
include "cn0.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "3eqtr2rd.mm"
include "simp3.mm"
include "odinf.mm"
include "iffalsed.mm"
include "eqtr4d.mm"
include "wo.mm"
include "odcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem dfod2
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cO: class O
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume odf1.1: |- X = ( Base ` G )
  assume odf1.2: |- O = ( od ` G )
  assume odf1.3: |- .x. = ( .g ` G )
  assume odf1.4: |- F = ( x e. ZZ |-> ( x .x. A ) )

  disjoint A x
  disjoint G x
  disjoint O x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G y
  disjoint G z
  disjoint O y
  disjoint O z
  disjoint .x. y
  disjoint .x. z
  disjoint X y
  disjoint X z
  disjoint F y
  disjoint F z
  assert |- ( ( G e. Grp /\ A e. X ) -> ( O ` A ) = if ( ran F e. Fin , ( # ` ran F ) , 0 ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @3
    cF
    crn
    #
    cfn
    wcel
    #
    @5
    chash
    cfv
    #
    cc0
    cif
    #
    wceq
    #
    @3
    cc0
    wceq
    #
    @2
    @4
    wa
    #
    @8
    @7
    c1
    @3
    cfz
    co
    #
    chash
    cfv
    #
    @3
    @11
    @6
    @7
    cc0
    @11
    cc0
    @3
    c1
    cmin
    co
    #
    cfz
    co
    #
    cfn
    wcel
    #
    @6
    @11
    cc0
    @14
    fzfid
    #
    @11
    @15
    @5
    cen
    wbr
    #
    @16
    @6
    wb
    @11
    @16
    @5
    cvv
    wcel
    #
    @15
    @5
    vy
    @15
    vy
    cv
    #
    cA
    c.x
    co
    #
    cmpt
    #
    wf1o
    #
    @18
    @17
    @11
    cz
    cX
    cF
    wf
    @5
    cX
    wss
    @19
    @11
    vx
    cz
    vx
    cv
    #
    cA
    c.x
    co
    #
    cX
    cF
    @2
    @24
    cz
    wcel
    #
    @25
    cX
    wcel
    #
    @4
    @0
    @26
    @1
    @27
    @0
    @26
    @1
    @27
    cX
    c.x
    cG
    @24
    cA
    odf1.1
    odf1.3
    mulgcl
    3expa
    an32s
    adantlr
    odf1.4
    fmptd
    cz
    cX
    cF
    frn
    @5
    cX
    cX
    cG
    cbs
    cfv
    cvv
    odf1.1
    cG
    cbs
    fvex
    eqeltri
    ssex
    3syl
    @11
    @21
    @5
    wcel
    #
    vy
    @15
    wral
    vz
    cv
    #
    @21
    wceq
    #
    vy
    @15
    wreu
    #
    vz
    @5
    wral
    #
    @23
    @11
    @28
    vy
    @15
    @11
    @20
    @15
    wcel
    #
    wa
    @20
    cz
    wcel
    #
    @21
    cvv
    wcel
    @28
    @33
    @34
    @11
    @20
    cc0
    @14
    elfzelz
    #
    adantl
    @20
    cA
    c.x
    ovex
    vx
    cz
    @25
    @21
    @20
    cF
    cvv
    odf1.4
    @24
    @20
    cA
    c.x
    oveq1
    elrnmpt1s
    sylancl
    ralrimiva
    @11
    @25
    @21
    wceq
    #
    vy
    @15
    wreu
    #
    vx
    cz
    wral
    #
    @32
    @11
    @37
    vx
    cz
    @11
    @26
    wa
    #
    @24
    @3
    cmo
    co
    #
    @15
    wcel
    #
    @36
    @20
    @40
    wceq
    #
    wb
    #
    vy
    @15
    wral
    @37
    @4
    @26
    @41
    @2
    @26
    @4
    @41
    @24
    @3
    zmodfz
    ancoms
    adantll
    @39
    @43
    vy
    @15
    @39
    @33
    wa
    #
    @40
    @20
    @3
    cmo
    co
    #
    wceq
    #
    @3
    @24
    @20
    cmin
    co
    cdvds
    wbr
    #
    @42
    @36
    @44
    @4
    @26
    @34
    @46
    @47
    wb
    @2
    @4
    @26
    @33
    simpllr
    #
    @11
    @26
    @33
    simplr
    #
    @33
    @34
    @39
    @35
    adantl
    #
    @24
    @20
    @3
    moddvds
    syl3anc
    @44
    @46
    @40
    @20
    wceq
    @42
    @44
    @45
    @20
    @40
    @44
    @20
    cr
    wcel
    @3
    crp
    wcel
    cc0
    @20
    cle
    wbr
    #
    @20
    @3
    clt
    wbr
    #
    @45
    @20
    wceq
    @44
    @20
    @50
    zred
    @44
    @3
    @48
    nnrpd
    @44
    @34
    @51
    @52
    @39
    @33
    @34
    @51
    @52
    w3a
    #
    @39
    cc0
    cz
    wcel
    @3
    cz
    wcel
    #
    @33
    @53
    wb
    0z
    @11
    @54
    @26
    @4
    @54
    @2
    @3
    nnz
    adantl
    #
    adantr
    @20
    cc0
    @3
    elfzm11
    sylancr
    biimpa
    #
    simp2d
    @44
    @34
    @51
    @52
    @56
    simp3d
    @20
    @3
    modid
    syl22anc
    eqeq2d
    @40
    @20
    eqcom
    syl6bb
    @44
    @0
    @1
    @26
    @34
    @47
    @36
    wb
    @0
    @1
    @4
    @26
    @33
    simp-4l
    @0
    @1
    @4
    @26
    @33
    simp-4r
    @49
    @50
    cA
    c.x
    cG
    @24
    @20
    cO
    cX
    cG
    c0g
    cfv
    #
    odf1.1
    odf1.2
    odf1.3
    @57
    eqid
    odcong
    syl112anc
    3bitr3rd
    ralrimiva
    @36
    vy
    @15
    @40
    reu6i
    syl2anc
    ralrimiva
    @25
    cvv
    wcel
    #
    vx
    cz
    wral
    @32
    @38
    wb
    @58
    vx
    cz
    @24
    cA
    c.x
    ovex
    rgenw
    @31
    @37
    vx
    vz
    cz
    @25
    cF
    cvv
    odf1.4
    @29
    @25
    wceq
    @30
    @36
    vy
    @15
    @29
    @25
    @21
    eqeq1
    reubidv
    ralrnmpt
    ax-mp
    sylibr
    vy
    vz
    @15
    @5
    @21
    @22
    @22
    eqid
    f1ompt
    sylanbrc
    @15
    @5
    @22
    cfn
    cvv
    f1oen2g
    syl3anc
    #
    @15
    @5
    enfi
    syl
    mpbid
    #
    iftrued
    @11
    @13
    @7
    wceq
    #
    @12
    @5
    cen
    wbr
    #
    @11
    @12
    @15
    cen
    wbr
    #
    @18
    @62
    @11
    @54
    @15
    @12
    cen
    wbr
    @63
    @55
    @3
    fz01en
    @15
    @12
    ensym
    3syl
    @59
    @12
    @15
    @5
    entr
    syl2anc
    @11
    @12
    cfn
    wcel
    @6
    @61
    @62
    wb
    @11
    c1
    @3
    fzfid
    @60
    @12
    @5
    hashen
    syl2anc
    mpbird
    @11
    @3
    cn0
    wcel
    #
    @13
    @3
    wceq
    @4
    @64
    @2
    @3
    nnnn0
    adantl
    @3
    hashfz1
    syl
    3eqtr2rd
    @0
    @1
    @10
    @9
    @0
    @1
    @10
    w3a
    #
    @3
    cc0
    @8
    @0
    @1
    @10
    simp3
    @65
    @6
    @7
    cc0
    vx
    cA
    c.x
    cF
    cG
    cO
    cX
    odf1.1
    odf1.2
    odf1.3
    odf1.4
    odinf
    iffalsed
    eqtr4d
    3expa
    @2
    @64
    @4
    @10
    wo
    @1
    @64
    @0
    cA
    cG
    cO
    cX
    odf1.1
    odf1.2
    odcl
    adantl
    @3
    elnn0
    sylib
    mpjaodan
end
