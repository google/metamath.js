include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ghmid.mm"
include "ad2antrr.mm"
include "eqeq2d.mm"
include "wb.mm"
include "simplr.mm"
include "simpr.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "grpidcl.mm"
include "syl.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "wf.mm"
include "ghmf.mm"
include "adantr.mm"
include "csg.mm"
include "eqid.mm"
include "ghmsub.mm"
include "3expb.mm"
include "adantlr.mm"
include "eqeq1d.mm"
include "grpsubcl.mm"
include "sylan.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sylbird.mm"
include "ghmgrp2.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "grpsubeq0.mm"
include "syl3anc.mm"
include "3imtr3d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem ghmf1
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume ghmf1.x: |- X = ( Base ` S )
  assume ghmf1.y: |- Y = ( Base ` T )
  assume ghmf1.z: |- .0. = ( 0g ` S )
  assume ghmf1.u: |- U = ( 0g ` T )

  disjoint F x
  disjoint S x
  disjoint T x
  disjoint U x
  disjoint X x
  disjoint Y x
  disjoint .0. x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint X y
  disjoint X z
  disjoint .0. y
  disjoint .0. z
  assert |- ( F e. ( S GrpHom T ) -> ( F : X -1-1-> Y <-> A. x e. X ( ( F ` x ) = U -> x = .0. ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cX
    cY
    cF
    wf1
    #
    vx
    cv
    #
    cF
    cfv
    #
    cU
    wceq
    #
    @2
    c.0
    wceq
    #
    wi
    #
    vx
    cX
    wral
    #
    @0
    @1
    wa
    #
    @6
    vx
    cX
    @8
    @2
    cX
    wcel
    #
    wa
    #
    @4
    @5
    @10
    @3
    c.0
    cF
    cfv
    #
    wceq
    #
    @4
    @5
    @10
    @11
    cU
    @3
    @0
    @11
    cU
    wceq
    @1
    @9
    cS
    cT
    cF
    c.0
    cU
    ghmf1.z
    ghmf1.u
    ghmid
    ad2antrr
    eqeq2d
    @10
    @1
    @9
    c.0
    cX
    wcel
    #
    @12
    @5
    wb
    @0
    @1
    @9
    simplr
    @8
    @9
    simpr
    @10
    cS
    cgrp
    wcel
    #
    @13
    @0
    @14
    @1
    @9
    cS
    cT
    cF
    ghmgrp1
    #
    ad2antrr
    cX
    cS
    c.0
    ghmf1.x
    ghmf1.z
    grpidcl
    syl
    cX
    cY
    @2
    c.0
    cF
    f1fveq
    syl12anc
    bitr3d
    biimpd
    ralrimiva
    @0
    @7
    wa
    #
    cX
    cY
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @18
    @20
    wceq
    #
    wi
    #
    vz
    cX
    wral
    vy
    cX
    wral
    @1
    @0
    @17
    @7
    cS
    cT
    cF
    cX
    cY
    ghmf1.x
    ghmf1.y
    ghmf
    #
    adantr
    @16
    @24
    vy
    vz
    cX
    cX
    @16
    @18
    cX
    wcel
    #
    @20
    cX
    wcel
    #
    wa
    #
    wa
    #
    @19
    @21
    cT
    csg
    cfv
    #
    co
    #
    cU
    wceq
    #
    @18
    @20
    cS
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @22
    @23
    @29
    @32
    @34
    cF
    cfv
    #
    cU
    wceq
    #
    @35
    @29
    @36
    @31
    cU
    @0
    @28
    @36
    @31
    wceq
    #
    @7
    @0
    @26
    @27
    @38
    cX
    cS
    cT
    @18
    cF
    @33
    @30
    @20
    ghmf1.x
    @33
    eqid
    #
    @30
    eqid
    #
    ghmsub
    3expb
    adantlr
    eqeq1d
    @29
    @34
    cX
    wcel
    #
    @7
    @37
    @35
    wi
    #
    @16
    @14
    @28
    @41
    @0
    @14
    @7
    @15
    adantr
    @14
    @26
    @27
    @41
    cX
    cS
    @33
    @18
    @20
    ghmf1.x
    @39
    grpsubcl
    3expb
    sylan
    @0
    @7
    @28
    simplr
    @6
    @42
    vx
    @34
    cX
    @2
    @34
    wceq
    #
    @4
    @37
    @5
    @35
    @43
    @3
    @36
    cU
    @2
    @34
    cF
    fveq2
    eqeq1d
    @2
    @34
    c.0
    eqeq1
    imbi12d
    rspcv
    sylc
    sylbird
    @29
    cT
    cgrp
    wcel
    #
    @19
    cY
    wcel
    @21
    cY
    wcel
    @32
    @22
    wb
    @0
    @44
    @7
    @28
    cS
    cT
    cF
    ghmgrp2
    ad2antrr
    @29
    cX
    cY
    @18
    cF
    @0
    @17
    @7
    @28
    @25
    ad2antrr
    #
    @16
    @26
    @27
    simprl
    #
    ffvelrnd
    @29
    cX
    cY
    @20
    cF
    @45
    @16
    @26
    @27
    simprr
    #
    ffvelrnd
    cY
    cT
    @30
    @19
    @21
    cU
    ghmf1.y
    ghmf1.u
    @40
    grpsubeq0
    syl3anc
    @29
    @14
    @26
    @27
    @35
    @23
    wb
    @0
    @14
    @7
    @28
    @15
    ad2antrr
    @46
    @47
    cX
    cS
    @33
    @18
    @20
    c.0
    ghmf1.x
    ghmf1.z
    @39
    grpsubeq0
    syl3anc
    3imtr3d
    ralrimivva
    vy
    vz
    cX
    cY
    cF
    dff13
    sylanbrc
    impbida
end
