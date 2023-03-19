include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wi.mm"
include "cminusg.mm"
include "cplusg.mm"
include "cpw.mm"
include "cres.mm"
include "simpr.mm"
include "adantr.mm"
include "simprl.mm"
include "wb.mm"
include "elpwg.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "adantl.mm"
include "3jca.mm"
include "simpl.mm"
include "a1i.mm"
include "eqid.mm"
include "lincdifsn.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "ad2antrl.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "ad2antll.mm"
include "com12.mm"
include "syl.mm"
include "imp.mm"
include "ssel2.mm"
include "lmodvscl.mm"
include "cvv.mm"
include "difexg.mm"
include "ssdifss.mm"
include "jca.mm"
include "lindslinindimp2lem2.mm"
include "syl13anc.mm"
include "lindslinindimp2lem3.mm"
include "lincfsuppcl.mm"
include "grpinvid2.mm"
include "bitr4d.mm"
include "eqcom.mm"
include "csca.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "lincval.mm"
include "fveq1i.mm"
include "fvres.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "ex.mm"
include "lmodvsneg.mm"
include "eqcomi.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "com23.mm"
include "3impia.mm"

theorem lindslinindimp2lem4
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cM: class M
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vs: setvar s
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )
  assume lindslinind.y: |- Y = ( ( invg ` R ) ` ( f ` x ) )
  assume lindslinind.g: |- G = ( f |` ( S \ { x } ) )

  disjoint G y
  disjoint B f
  disjoint B y
  disjoint f y
  disjoint M f
  disjoint M y
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint V y
  disjoint Z f
  disjoint Z y
  disjoint .0. f
  disjoint .0. x
  disjoint .0. y
  disjoint B g
  disjoint B s
  disjoint B z
  disjoint f g
  disjoint f s
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint s y
  disjoint s z
  disjoint y z
  disjoint M g
  disjoint M s
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S g
  disjoint S s
  disjoint S z
  disjoint g x
  disjoint s x
  disjoint V g
  disjoint V s
  disjoint V z
  disjoint Z g
  disjoint Z s
  disjoint .0. g
  disjoint .0. s
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. V /\ M e. LMod ) /\ ( S C_ ( Base ` M ) /\ x e. S ) /\ ( f e. ( B ^m S ) /\ f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) ) -> ( M gsum ( y e. ( S \ { x } ) |-> ( ( f ` y ) ( .s ` M ) y ) ) ) = ( Y ( .s ` M ) x ) )

  proof
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    cS
    wcel
    #
    wa
    #
    vf
    cv
    #
    cB
    cS
    cmap
    co
    wcel
    #
    @8
    c.0
    cfsupp
    wbr
    #
    @8
    cS
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    w3a
    #
    cM
    vy
    cS
    @5
    csn
    #
    cdif
    #
    vy
    cv
    #
    @8
    cfv
    #
    @17
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cY
    @5
    @19
    co
    #
    wceq
    #
    @14
    @2
    @7
    wa
    #
    @24
    @9
    @10
    @13
    @25
    @24
    wi
    @9
    @10
    wa
    #
    @25
    @13
    @24
    @26
    @25
    @13
    @24
    wi
    @26
    @25
    wa
    #
    @13
    @5
    @8
    cfv
    #
    @5
    @19
    co
    #
    cM
    cminusg
    cfv
    #
    cfv
    #
    cG
    @16
    @11
    co
    #
    wceq
    #
    @24
    @27
    @13
    @32
    @29
    cM
    cplusg
    cfv
    #
    co
    #
    cZ
    wceq
    #
    @33
    @27
    @12
    @35
    cZ
    @27
    @1
    cS
    @3
    cpw
    #
    wcel
    #
    @6
    w3a
    #
    @26
    cG
    @8
    @16
    cres
    #
    wceq
    #
    @12
    @35
    wceq
    @25
    @39
    @26
    @25
    @1
    @38
    @6
    @2
    @1
    @7
    @0
    @1
    simpr
    #
    adantr
    @25
    @38
    @4
    @2
    @4
    @6
    simprl
    @0
    @38
    @4
    wb
    @1
    @7
    cS
    @3
    cV
    elpwg
    ad2antrr
    mpbird
    @7
    @6
    @2
    @4
    @6
    simpr
    #
    adantl
    3jca
    adantl
    @26
    @25
    simpl
    #
    @41
    @27
    lindslinind.g
    a1i
    @3
    @34
    cR
    cB
    @19
    @8
    cG
    cM
    cS
    @5
    c.0
    @3
    eqid
    #
    lindslinind.r
    lindslinind.b
    @19
    eqid
    #
    @34
    eqid
    #
    lindslinind.0
    lincdifsn
    syl3anc
    eqeq1d
    @27
    cM
    cgrp
    wcel
    #
    @29
    @3
    wcel
    #
    @32
    @3
    wcel
    #
    @33
    @36
    wb
    @2
    @48
    @26
    @7
    @1
    @48
    @0
    cM
    lmodgrp
    adantl
    ad2antrl
    @27
    @1
    @28
    cB
    wcel
    #
    @5
    @3
    wcel
    #
    @49
    @2
    @1
    @26
    @7
    @42
    ad2antrl
    #
    @26
    @25
    @51
    @9
    @25
    @51
    wi
    #
    @10
    @9
    cS
    cB
    @8
    wf
    #
    @54
    @8
    cB
    cS
    elmapi
    #
    @25
    @55
    @51
    @6
    @55
    @51
    wi
    @2
    @4
    @55
    @6
    @51
    cS
    cB
    @5
    @8
    ffvelrn
    #
    expcom
    ad2antll
    com12
    syl
    adantr
    imp
    @7
    @52
    @26
    @2
    cS
    @3
    @5
    ssel2
    ad2antll
    #
    @28
    @19
    cR
    cB
    @3
    cM
    @5
    @45
    lindslinind.r
    @46
    lindslinind.b
    lmodvscl
    syl3anc
    @27
    @1
    @16
    cvv
    wcel
    #
    @16
    @3
    wss
    #
    wa
    #
    cG
    cB
    @16
    cmap
    co
    #
    wcel
    #
    cG
    c.0
    cfsupp
    wbr
    #
    wa
    @50
    @53
    @25
    @61
    @26
    @25
    @59
    @60
    @0
    @59
    @1
    @7
    cS
    @15
    cV
    difexg
    ad2antrr
    #
    @4
    @60
    @2
    @6
    cS
    @3
    @15
    ssdifss
    ad2antrl
    #
    jca
    adantl
    @27
    @63
    @64
    @27
    @2
    @4
    @6
    @9
    @63
    @26
    @2
    @7
    simprl
    #
    @7
    @4
    @26
    @2
    @4
    @6
    simpl
    ad2antll
    @7
    @6
    @26
    @2
    @43
    ad2antll
    @26
    @9
    @25
    @9
    @10
    simpl
    adantr
    vx
    cB
    cR
    cS
    vf
    cG
    cM
    cV
    cY
    c.0
    cZ
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    lindslinind.y
    lindslinind.g
    lindslinindimp2lem2
    syl13anc
    #
    @27
    @2
    @7
    @26
    @64
    @67
    @25
    @7
    @26
    @2
    @7
    simpr
    adantl
    @44
    vx
    cB
    cR
    cS
    vf
    cG
    cM
    cV
    cY
    c.0
    cZ
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    lindslinind.y
    lindslinind.g
    lindslinindimp2lem3
    syl3anc
    jca
    @3
    cR
    cB
    cG
    cM
    @16
    cvv
    c.0
    @45
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lincfsuppcl
    syl3anc
    @3
    @34
    cM
    @30
    @29
    @32
    cZ
    @45
    @47
    lindslinind.z
    @30
    eqid
    #
    grpinvid2
    syl3anc
    bitr4d
    @33
    @32
    @31
    wceq
    #
    @27
    @24
    @31
    @32
    eqcom
    @27
    @70
    cM
    vy
    @16
    @17
    cG
    cfv
    #
    @17
    @19
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @31
    wceq
    #
    @24
    @27
    @32
    @74
    @31
    @27
    @1
    cG
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @16
    cmap
    co
    #
    wcel
    @16
    @37
    wcel
    #
    @32
    @74
    wceq
    @53
    @27
    cG
    @62
    @78
    @68
    cB
    @77
    @16
    cmap
    cB
    cR
    cbs
    cfv
    @77
    lindslinind.b
    cR
    @76
    cbs
    lindslinind.r
    fveq2i
    eqtri
    oveq1i
    syl6eleq
    @25
    @79
    @26
    @25
    @79
    @60
    @66
    @25
    @59
    @79
    @60
    wb
    @65
    @16
    @3
    cvv
    elpwg
    syl
    mpbird
    adantl
    vy
    cG
    cM
    @16
    clmod
    lincval
    syl3anc
    eqeq1d
    @27
    @75
    @24
    @27
    @74
    @22
    @31
    @23
    @27
    @73
    @21
    cM
    cgsu
    @27
    vy
    @16
    @72
    @20
    @27
    @17
    @16
    wcel
    #
    wa
    #
    @71
    @18
    @17
    @19
    @81
    @71
    @17
    @40
    cfv
    #
    @18
    @71
    @82
    wceq
    @81
    @17
    cG
    @40
    lindslinind.g
    fveq1i
    a1i
    @80
    @82
    @18
    wceq
    @27
    @17
    @16
    @8
    fvres
    adantl
    eqtrd
    oveq1d
    mpteq2dva
    oveq2d
    @27
    @31
    @28
    cR
    cminusg
    cfv
    #
    cfv
    #
    @5
    @19
    co
    @23
    @27
    @3
    @28
    @19
    cR
    cB
    @83
    @30
    cM
    @5
    @45
    lindslinind.r
    @46
    @69
    lindslinind.b
    @83
    eqid
    @53
    @58
    @26
    @25
    @51
    @9
    @54
    @10
    @25
    @9
    @51
    @6
    @9
    @51
    wi
    @2
    @4
    @9
    @6
    @51
    @9
    @55
    @6
    @51
    wi
    @56
    @55
    @6
    @51
    @57
    ex
    syl
    com12
    ad2antll
    com12
    adantr
    imp
    lmodvsneg
    @27
    @84
    cY
    @5
    @19
    @84
    cY
    wceq
    @27
    cY
    @84
    lindslinind.y
    eqcomi
    a1i
    oveq1d
    eqtrd
    eqeq12d
    biimpd
    sylbid
    syl5bi
    sylbid
    ex
    com23
    3impia
    com12
    3impia
end
