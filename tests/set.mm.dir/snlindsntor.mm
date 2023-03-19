include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cpw.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cmap.mm"
include "clininds.mm"
include "wn.mm"
include "df-ne.mm"
include "ralbii.mm"
include "raldifsni.mm"
include "bitri.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "simpl.mm"
include "adantr.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "snelpwi.mm"
include "eleq2s.mm"
include "ad3antlr.mm"
include "lincval.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "wf.mm"
include "elmapi.mm"
include "snidg.mm"
include "ffvelrn.mm"
include "sylan2.mm"
include "simprlr.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "expcom.mm"
include "syl5com.mm"
include "impcom.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "gsumsn.mm"
include "oveqi.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl5bir.mm"
include "ex.mm"
include "syl56.mm"
include "com23.mm"
include "imp31.mm"
include "sylbid.mm"
include "adantld.mm"
include "ralrimiva.mm"
include "impexp.mm"
include "cvv.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fdmfifsupp.mm"
include "pm2.27.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "snlindsntorlem.mm"
include "syld.mm"
include "impbid.mm"
include "wb.mm"
include "ralsng.mm"
include "bicomd.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "biantrurd.mm"
include "3bitrd.mm"
include "syl5bb.mm"
include "snex.mm"
include "islininds.mm"
include "sylancr.mm"
include "bitr4d.mm"

theorem snlindsntor
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cM: class M
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume snlindsntor.b: |- B = ( Base ` M )
  assume snlindsntor.r: |- R = ( Scalar ` M )
  assume snlindsntor.s: |- S = ( Base ` R )
  assume snlindsntor.0: |- .0. = ( 0g ` R )
  assume snlindsntor.z: |- Z = ( 0g ` M )
  assume snlindsntor.t: |- .x. = ( .s ` M )

  disjoint B s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint Z s
  disjoint .x. s
  disjoint .0. s
  disjoint B f
  disjoint f s
  disjoint M f
  disjoint M x
  disjoint M y
  disjoint f x
  disjoint f y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint S f
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Z f
  disjoint .x. f
  disjoint .0. f
  disjoint B x
  disjoint .0. y
  disjoint k x
  assert |- ( ( M e. LMod /\ X e. B ) -> ( A. s e. ( S \ { .0. } ) ( s .x. X ) =/= Z <-> { X } linIndS M ) )

  proof
    cM
    clmod
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vs
    cv
    #
    cX
    c.x
    co
    #
    cZ
    wne
    #
    vs
    cS
    c.0
    csn
    cdif
    #
    wral
    #
    cX
    csn
    #
    cB
    cpw
    wcel
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @10
    @8
    cM
    clinc
    cfv
    co
    #
    cZ
    wceq
    #
    wa
    #
    vy
    cv
    #
    @10
    cfv
    #
    c.0
    wceq
    #
    vy
    @8
    wral
    #
    wi
    #
    vf
    cS
    @8
    cmap
    co
    #
    wral
    #
    wa
    #
    @8
    cM
    clininds
    wbr
    #
    @7
    @4
    cZ
    wceq
    #
    @3
    c.0
    wceq
    #
    wi
    #
    vs
    cS
    wral
    #
    @2
    @22
    @7
    @24
    wn
    #
    vs
    @6
    wral
    @27
    @5
    @28
    vs
    @6
    @4
    cZ
    df-ne
    ralbii
    @24
    vs
    cS
    c.0
    raldifsni
    bitri
    @2
    @27
    @14
    cX
    @10
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vf
    @20
    wral
    #
    @21
    @22
    @2
    @27
    @32
    @2
    @27
    @32
    @2
    @27
    wa
    #
    @31
    vf
    @20
    @33
    @10
    @20
    wcel
    #
    wa
    #
    @14
    @11
    cM
    vx
    @8
    vx
    cv
    #
    @10
    cfv
    #
    @36
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cZ
    wceq
    #
    wa
    @30
    @35
    @13
    @41
    @11
    @35
    @12
    @40
    cZ
    @35
    @0
    @10
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @8
    cmap
    co
    #
    wcel
    #
    @8
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @12
    @40
    wceq
    @33
    @0
    @34
    @2
    @0
    @27
    @0
    @1
    simpl
    #
    adantr
    #
    adantr
    @34
    @45
    @33
    @34
    @45
    @20
    @44
    @10
    cS
    @43
    @8
    cmap
    cS
    cR
    cbs
    cfv
    @43
    snlindsntor.s
    cR
    @42
    cbs
    snlindsntor.r
    fveq2i
    eqtri
    oveq1i
    eleq2i
    biimpi
    adantl
    @1
    @47
    @0
    @27
    @34
    @47
    cX
    @46
    cB
    cX
    @46
    snelpwi
    snlindsntor.b
    eleq2s
    ad3antlr
    vx
    @10
    cM
    @8
    clmod
    lincval
    syl3anc
    eqeq1d
    anbi2d
    @35
    @41
    @30
    @11
    @35
    @41
    @29
    cX
    @38
    co
    #
    cZ
    wceq
    #
    @30
    @35
    @40
    @50
    cZ
    @35
    cM
    cmnd
    wcel
    #
    @1
    @50
    cB
    wcel
    #
    @40
    @50
    wceq
    @0
    @52
    @1
    @27
    @34
    @0
    cM
    cgrp
    wcel
    @52
    cM
    lmodgrp
    cM
    grpmnd
    syl
    ad3antrrr
    @0
    @1
    @27
    @34
    simpllr
    @34
    @33
    @53
    @34
    @8
    cS
    @10
    wf
    #
    @33
    @53
    @10
    cS
    @8
    elmapi
    #
    @54
    @33
    @53
    @54
    @33
    wa
    @0
    @29
    cS
    wcel
    #
    @1
    @53
    @33
    @0
    @54
    @49
    adantl
    @33
    @54
    cX
    @8
    wcel
    #
    @56
    @2
    @57
    @27
    @1
    @57
    @0
    cX
    cB
    snidg
    #
    adantl
    adantr
    @8
    cS
    cX
    @10
    ffvelrn
    #
    sylan2
    @54
    @0
    @1
    @27
    simprlr
    @29
    @38
    cR
    cS
    cB
    cM
    cX
    snlindsntor.b
    snlindsntor.r
    @38
    eqid
    snlindsntor.s
    lmodvscl
    syl3anc
    expcom
    syl5com
    impcom
    @39
    cB
    @50
    vx
    cM
    cX
    cB
    snlindsntor.b
    @36
    cX
    wceq
    #
    @37
    @29
    @36
    cX
    @38
    @36
    cX
    @10
    fveq2
    @60
    id
    oveq12d
    gsumsn
    syl3anc
    eqeq1d
    @2
    @27
    @34
    @51
    @30
    wi
    #
    @2
    @34
    @27
    @61
    @34
    @54
    @2
    @56
    @27
    @61
    wi
    @55
    @1
    @54
    @56
    wi
    @0
    @54
    @1
    @56
    @1
    @54
    @57
    @56
    @58
    @59
    sylan2
    expcom
    adantl
    @56
    @27
    @61
    @51
    @29
    cX
    c.x
    co
    #
    cZ
    wceq
    #
    @56
    @27
    wa
    @30
    @62
    @50
    cZ
    c.x
    @38
    @29
    cX
    snlindsntor.t
    oveqi
    eqeq1i
    @26
    @63
    @30
    wi
    vs
    @29
    cS
    @3
    @29
    wceq
    #
    @24
    @63
    @25
    @30
    @64
    @4
    @62
    cZ
    @3
    @29
    cX
    c.x
    oveq1
    eqeq1d
    @3
    @29
    c.0
    eqeq1
    imbi12d
    rspcva
    syl5bir
    ex
    syl56
    com23
    imp31
    sylbid
    adantld
    sylbid
    ralrimiva
    ex
    @2
    @32
    @13
    @30
    wi
    #
    vf
    @20
    wral
    @27
    @2
    @31
    @65
    vf
    @20
    @31
    @11
    @65
    wi
    #
    @2
    @34
    wa
    #
    @65
    @11
    @13
    @30
    impexp
    @67
    @11
    @66
    @65
    wi
    @67
    @8
    cS
    @10
    cvv
    c.0
    @34
    @54
    @2
    @55
    adantl
    @8
    cfn
    wcel
    @67
    cX
    snfi
    a1i
    c.0
    cvv
    wcel
    @67
    c.0
    cR
    c0g
    cfv
    cvv
    snlindsntor.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fdmfifsupp
    @11
    @65
    pm2.27
    syl
    syl5bi
    ralimdva
    cB
    cR
    cS
    c.x
    vf
    cM
    cX
    c.0
    cZ
    vs
    snlindsntor.b
    snlindsntor.r
    snlindsntor.s
    snlindsntor.0
    snlindsntor.z
    snlindsntor.t
    snlindsntorlem
    syld
    impbid
    @2
    @31
    @19
    vf
    @20
    @2
    @30
    @18
    @14
    @2
    @18
    @30
    @1
    @18
    @30
    wb
    @0
    @17
    @30
    vy
    cX
    cB
    @15
    cX
    wceq
    @16
    @29
    c.0
    @15
    cX
    @10
    fveq2
    eqeq1d
    ralsng
    adantl
    bicomd
    imbi2d
    ralbidv
    @2
    @9
    @21
    @1
    @9
    @0
    cX
    cB
    snelpwi
    adantl
    biantrurd
    3bitrd
    syl5bb
    @2
    @8
    cvv
    wcel
    @0
    @23
    @22
    wb
    cX
    snex
    @48
    vy
    cB
    cR
    @8
    vf
    cS
    cM
    cvv
    clmod
    c.0
    cZ
    snlindsntor.b
    snlindsntor.z
    snlindsntor.r
    snlindsntor.s
    snlindsntor.0
    islininds
    sylancr
    bitr4d
end
