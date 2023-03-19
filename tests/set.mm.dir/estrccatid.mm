include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "cvv.mm"
include "id.mm"
include "estrcbas.mm"
include "eqidd.mm"
include "cestrc.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "biid.mm"
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "simpl.mm"
include "eqid.mm"
include "simpr.mm"
include "elestrchom.mm"
include "mpbird.mm"
include "cop.mm"
include "ccom.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "simpr31.mm"
include "mpbid.mm"
include "estrcco.mm"
include "wceq.mm"
include "fcoi2.mm"
include "syl.mm"
include "eqtrd.mm"
include "simpr2l.mm"
include "simpr32.mm"
include "fcoi1.mm"
include "fco.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "coass.mm"
include "simpr2r.mm"
include "simpr33.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "iscatd2.mm"

theorem estrccatid
  let vx: setvar x
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume estrccat.c: |- C = ( ExtStrCat ` U )

  disjoint C x
  disjoint U x
  disjoint V x
  disjoint f g
  disjoint f h
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint C g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint C h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint V f
  disjoint V g
  disjoint V h
  disjoint V w
  disjoint V y
  disjoint V z
  assert |- ( U e. V -> ( C e. Cat /\ ( Id ` C ) = ( x e. U |-> ( _I |` ( Base ` x ) ) ) ) )

  proof
    cU
    cV
    wcel
    #
    vw
    cv
    #
    cU
    wcel
    #
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    vy
    cv
    #
    cU
    wcel
    #
    vz
    cv
    #
    cU
    wcel
    #
    wa
    #
    vf
    cv
    #
    @1
    @3
    cC
    chom
    cfv
    #
    co
    wcel
    #
    vg
    cv
    #
    @3
    @6
    @12
    co
    wcel
    #
    vh
    cv
    #
    @6
    @8
    @12
    co
    wcel
    #
    w3a
    #
    w3a
    #
    vw
    vx
    vy
    vz
    cU
    cC
    cC
    cco
    cfv
    #
    cid
    @3
    cbs
    cfv
    #
    cres
    #
    vf
    vg
    vh
    @12
    cvv
    @0
    cC
    cU
    cV
    estrccat.c
    @0
    id
    estrcbas
    @0
    @12
    eqidd
    @0
    @20
    eqidd
    cC
    cvv
    wcel
    @0
    cC
    cU
    cestrc
    cfv
    cvv
    estrccat.c
    cU
    cestrc
    fvex
    eqeltri
    a1i
    @19
    biid
    @0
    @4
    wa
    #
    @22
    @3
    @3
    @12
    co
    wcel
    @21
    @21
    @22
    wf
    #
    @21
    @21
    @22
    wf1o
    #
    @24
    @23
    @21
    f1oi
    #
    @21
    @21
    @22
    f1of
    #
    mp1i
    @23
    @21
    @21
    cC
    cU
    @22
    @12
    cV
    @3
    @3
    estrccat.c
    @0
    @4
    simpl
    @12
    eqid
    #
    @0
    @4
    simpr
    #
    @29
    @21
    eqid
    #
    @30
    elestrchom
    mpbird
    @0
    @19
    wa
    #
    @22
    @11
    @1
    @3
    cop
    #
    @3
    @20
    co
    co
    @22
    @11
    ccom
    #
    @11
    @31
    @1
    cbs
    cfv
    #
    @21
    cC
    @21
    @20
    cU
    @11
    @22
    cV
    @1
    @3
    @3
    estrccat.c
    @0
    @19
    simpl
    #
    @20
    eqid
    #
    @2
    @4
    @10
    @18
    @0
    simpr1l
    #
    @2
    @4
    @10
    @18
    @0
    simpr1r
    #
    @38
    @34
    eqid
    #
    @30
    @30
    @31
    @13
    @34
    @21
    @11
    wf
    #
    @13
    @15
    @17
    @5
    @10
    @0
    simpr31
    @31
    @34
    @21
    cC
    cU
    @11
    @12
    cV
    @1
    @3
    estrccat.c
    @35
    @28
    @37
    @38
    @39
    @30
    elestrchom
    mpbid
    #
    @25
    @24
    @31
    @26
    @27
    mp1i
    #
    estrcco
    @31
    @40
    @33
    @11
    wceq
    @41
    @34
    @21
    @11
    fcoi2
    syl
    eqtrd
    @31
    @14
    @22
    @3
    @3
    cop
    @6
    @20
    co
    co
    @14
    @22
    ccom
    #
    @14
    @31
    @21
    @21
    cC
    @6
    cbs
    cfv
    #
    @20
    cU
    @22
    @14
    cV
    @3
    @3
    @6
    estrccat.c
    @35
    @36
    @38
    @38
    @7
    @9
    @5
    @18
    @0
    simpr2l
    #
    @30
    @30
    @44
    eqid
    #
    @42
    @31
    @15
    @21
    @44
    @14
    wf
    #
    @13
    @15
    @17
    @5
    @10
    @0
    simpr32
    @31
    @21
    @44
    cC
    cU
    @14
    @12
    cV
    @3
    @6
    estrccat.c
    @35
    @28
    @38
    @45
    @30
    @46
    elestrchom
    mpbid
    #
    estrcco
    @31
    @47
    @43
    @14
    wceq
    @48
    @21
    @44
    @14
    fcoi1
    syl
    eqtrd
    @31
    @14
    @11
    @32
    @6
    @20
    co
    co
    #
    @14
    @11
    ccom
    #
    @1
    @6
    @12
    co
    #
    @31
    @34
    @21
    cC
    @44
    @20
    cU
    @11
    @14
    cV
    @1
    @3
    @6
    estrccat.c
    @35
    @36
    @37
    @38
    @45
    @39
    @30
    @46
    @41
    @48
    estrcco
    #
    @31
    @50
    @51
    wcel
    @34
    @44
    @50
    wf
    #
    @31
    @47
    @40
    @53
    @48
    @41
    @34
    @21
    @44
    @14
    @11
    fco
    syl2anc
    #
    @31
    @34
    @44
    cC
    cU
    @50
    @12
    cV
    @1
    @6
    estrccat.c
    @35
    @28
    @37
    @45
    @39
    @46
    elestrchom
    mpbird
    eqeltrd
    @31
    @16
    @14
    ccom
    #
    @11
    @32
    @8
    @20
    co
    #
    co
    #
    @16
    @50
    @1
    @6
    cop
    @8
    @20
    co
    #
    co
    #
    @16
    @14
    @3
    @6
    cop
    @8
    @20
    co
    co
    #
    @11
    @56
    co
    @16
    @49
    @58
    co
    @31
    @55
    @11
    ccom
    @16
    @50
    ccom
    @57
    @59
    @16
    @14
    @11
    coass
    @31
    @34
    @21
    cC
    @8
    cbs
    cfv
    #
    @20
    cU
    @11
    @55
    cV
    @1
    @3
    @8
    estrccat.c
    @35
    @36
    @37
    @38
    @7
    @9
    @5
    @18
    @0
    simpr2r
    #
    @39
    @30
    @61
    eqid
    #
    @41
    @31
    @44
    @61
    @16
    wf
    #
    @47
    @21
    @61
    @55
    wf
    @31
    @17
    @64
    @13
    @15
    @17
    @5
    @10
    @0
    simpr33
    @31
    @44
    @61
    cC
    cU
    @16
    @12
    cV
    @6
    @8
    estrccat.c
    @35
    @28
    @45
    @62
    @46
    @63
    elestrchom
    mpbid
    #
    @48
    @21
    @44
    @61
    @16
    @14
    fco
    syl2anc
    estrcco
    @31
    @34
    @44
    cC
    @61
    @20
    cU
    @50
    @16
    cV
    @1
    @6
    @8
    estrccat.c
    @35
    @36
    @37
    @45
    @62
    @39
    @46
    @63
    @54
    @65
    estrcco
    3eqtr4a
    @31
    @60
    @55
    @11
    @56
    @31
    @21
    @44
    cC
    @61
    @20
    cU
    @14
    @16
    cV
    @3
    @6
    @8
    estrccat.c
    @35
    @36
    @38
    @45
    @62
    @30
    @46
    @63
    @48
    @65
    estrcco
    oveq1d
    @31
    @49
    @50
    @16
    @58
    @52
    oveq2d
    3eqtr4d
    iscatd2
end
