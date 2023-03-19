include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "ccat.mm"
include "w3a.mm"
include "wa.mm"
include "simpr.mm"
include "subcssc.mm"
include "adantr.mm"
include "cxp.mm"
include "wfn.mm"
include "ad2antrr.mm"
include "subcidcl.mm"
include "ralrimiva.mm"
include "subccat.mm"
include "3jca.mm"
include "cop.mm"
include "cco.mm"
include "simpr1.mm"
include "simpr2.mm"
include "chom.mm"
include "cbs.mm"
include "eqid.mm"
include "simplrr.mm"
include "simprl1.mm"
include "homffn.mm"
include "a1i.mm"
include "simplrl.mm"
include "ssc1.mm"
include "rescbas.mm"
include "eleqtrd.mm"
include "simprl2.mm"
include "simprl3.mm"
include "simprrl.mm"
include "reschom.mm"
include "oveqd.mm"
include "simprrr.mm"
include "catcocl.mm"
include "rescco.mm"
include "3eltr4d.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "ralrimivvva.mm"
include "3adantr2.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "issubc2.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem issubc3
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let cH: class H
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  assume issubc3.h: |- H = ( Homf ` C )
  assume issubc3.i: |- .1. = ( Id ` C )
  assume issubc3.1: |- D = ( C |`cat J )
  assume issubc3.c: |- ( ph -> C e. Cat )
  assume issubc3.a: |- ( ph -> J Fn ( S X. S ) )

  disjoint C x
  disjoint D x
  disjoint H x
  disjoint ph x
  disjoint J x
  disjoint S x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D f
  disjoint D g
  disjoint D y
  disjoint D z
  disjoint H f
  disjoint H g
  disjoint H y
  disjoint H z
  disjoint f ph
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J g
  disjoint J y
  disjoint J z
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\ A. x e. S ( .1. ` x ) e. ( x J x ) /\ D e. Cat ) ) )

  proof
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    cJ
    cH
    cssc
    wbr
    #
    vx
    cv
    #
    c.1
    cfv
    @2
    @2
    cJ
    co
    wcel
    #
    vx
    cS
    wral
    #
    cD
    ccat
    wcel
    #
    w3a
    #
    wph
    @0
    wa
    #
    @1
    @4
    @5
    @7
    cC
    cH
    cJ
    wph
    @0
    simpr
    #
    issubc3.h
    subcssc
    @7
    @3
    vx
    cS
    @7
    @2
    cS
    wcel
    #
    wa
    cC
    cS
    c.1
    cJ
    @2
    @7
    @0
    @9
    @8
    adantr
    wph
    cJ
    cS
    cS
    cxp
    wfn
    #
    @0
    @9
    issubc3.a
    ad2antrr
    @7
    @9
    simpr
    issubc3.i
    subcidcl
    ralrimiva
    @7
    cC
    cD
    cJ
    issubc3.1
    @8
    subccat
    3jca
    wph
    @6
    wa
    #
    @0
    @1
    @3
    vg
    cv
    #
    vf
    cv
    #
    @2
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @2
    @16
    cJ
    co
    #
    wcel
    #
    vg
    @14
    @16
    cJ
    co
    #
    wral
    vf
    @2
    @14
    cJ
    co
    #
    wral
    #
    vz
    cS
    wral
    vy
    cS
    wral
    #
    wa
    vx
    cS
    wral
    #
    wph
    @1
    @4
    @5
    simpr1
    @11
    @4
    @25
    vx
    cS
    wral
    #
    @26
    wph
    @1
    @4
    @5
    simpr2
    wph
    @1
    @5
    @27
    @4
    wph
    @1
    @5
    wa
    #
    wa
    #
    @24
    vx
    vy
    vz
    cS
    cS
    cS
    @29
    @9
    @14
    cS
    wcel
    #
    @16
    cS
    wcel
    #
    w3a
    #
    wa
    @21
    vf
    vg
    @23
    @22
    @29
    @32
    @13
    @23
    wcel
    #
    @12
    @22
    wcel
    #
    wa
    #
    @21
    @29
    @32
    @35
    wa
    #
    wa
    #
    @12
    @13
    @15
    @16
    cD
    cco
    cfv
    #
    co
    #
    co
    @2
    @16
    cD
    chom
    cfv
    #
    co
    @19
    @20
    @37
    cD
    cbs
    cfv
    #
    cD
    @38
    @13
    @12
    @40
    @2
    @14
    @16
    @41
    eqid
    @40
    eqid
    @38
    eqid
    wph
    @1
    @5
    @36
    simplrr
    @37
    @2
    cS
    @41
    @9
    @30
    @31
    @35
    @29
    simprl1
    @37
    cC
    cbs
    cfv
    #
    cC
    cD
    cS
    cJ
    ccat
    issubc3.1
    @42
    eqid
    #
    wph
    cC
    ccat
    wcel
    #
    @28
    @36
    issubc3.c
    ad2antrr
    #
    wph
    @10
    @28
    @36
    issubc3.a
    ad2antrr
    #
    @37
    cS
    @42
    cJ
    cH
    @46
    cH
    @42
    @42
    cxp
    wfn
    @37
    @42
    cC
    cH
    issubc3.h
    @43
    homffn
    a1i
    wph
    @1
    @5
    @36
    simplrl
    ssc1
    #
    rescbas
    #
    eleqtrd
    @37
    @14
    cS
    @41
    @9
    @30
    @31
    @35
    @29
    simprl2
    @48
    eleqtrd
    @37
    @16
    cS
    @41
    @9
    @30
    @31
    @35
    @29
    simprl3
    @48
    eleqtrd
    @37
    @13
    @23
    @2
    @14
    @40
    co
    @29
    @32
    @33
    @34
    simprrl
    @37
    cJ
    @40
    @2
    @14
    @37
    @42
    cC
    cD
    cS
    cJ
    ccat
    issubc3.1
    @43
    @45
    @46
    @47
    reschom
    #
    oveqd
    eleqtrd
    @37
    @12
    @22
    @14
    @16
    @40
    co
    @29
    @32
    @33
    @34
    simprrr
    @37
    cJ
    @40
    @14
    @16
    @49
    oveqd
    eleqtrd
    catcocl
    @37
    @18
    @39
    @12
    @13
    @37
    @17
    @38
    @15
    @16
    @37
    @42
    cC
    cD
    cS
    @17
    cJ
    ccat
    issubc3.1
    @43
    @45
    @46
    @47
    @17
    eqid
    #
    rescco
    oveqd
    oveqd
    @37
    cJ
    @40
    @2
    @16
    @49
    oveqd
    3eltr4d
    anassrs
    ralrimivva
    ralrimivvva
    3adantr2
    @3
    @25
    vx
    cS
    r19.26
    sylanbrc
    @11
    vx
    vy
    vz
    cC
    cS
    @17
    c.1
    vf
    vg
    cH
    cJ
    issubc3.h
    issubc3.i
    @50
    wph
    @44
    @6
    issubc3.c
    adantr
    wph
    @10
    @6
    issubc3.a
    adantr
    issubc2
    mpbir2and
    impbida
end
