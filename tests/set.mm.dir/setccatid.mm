include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "id.mm"
include "setcbas.mm"
include "eqidd.mm"
include "csetc.mm"
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
include "elsetchom.mm"
include "mpbird.mm"
include "cop.mm"
include "ccom.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "simpr31.mm"
include "mpbid.mm"
include "setcco.mm"
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

theorem setccatid
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
  let wph: wff ph
  let cX: class X
  assume setccat.c: |- C = ( SetCat ` U )

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
  disjoint ph x
  disjoint X x
  assert |- ( U e. V -> ( C e. Cat /\ ( Id ` C ) = ( x e. U |-> ( _I |` x ) ) ) )

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
    setccat.c
    @0
    id
    setcbas
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
    csetc
    cfv
    cvv
    setccat.c
    cU
    csetc
    fvex
    eqeltri
    a1i
    @19
    biid
    @0
    @4
    wa
    #
    @21
    @3
    @3
    @12
    co
    wcel
    @3
    @3
    @21
    wf
    #
    @3
    @3
    @21
    wf1o
    #
    @23
    @22
    @3
    f1oi
    #
    @3
    @3
    @21
    f1of
    #
    mp1i
    @22
    cC
    cU
    @21
    @12
    cV
    @3
    @3
    setccat.c
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
    @28
    elsetchom
    mpbird
    @0
    @19
    wa
    #
    @21
    @11
    @1
    @3
    cop
    #
    @3
    @20
    co
    co
    @21
    @11
    ccom
    #
    @11
    @29
    cC
    @20
    cU
    @11
    @21
    cV
    @1
    @3
    @3
    setccat.c
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
    @35
    @29
    @13
    @1
    @3
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
    @29
    cC
    cU
    @11
    @12
    cV
    @1
    @3
    setccat.c
    @32
    @27
    @34
    @35
    elsetchom
    mpbid
    #
    @24
    @23
    @29
    @25
    @26
    mp1i
    #
    setcco
    @29
    @36
    @31
    @11
    wceq
    @37
    @1
    @3
    @11
    fcoi2
    syl
    eqtrd
    @29
    @14
    @21
    @3
    @3
    cop
    @6
    @20
    co
    co
    @14
    @21
    ccom
    #
    @14
    @29
    cC
    @20
    cU
    @21
    @14
    cV
    @3
    @3
    @6
    setccat.c
    @32
    @33
    @35
    @35
    @7
    @9
    @5
    @18
    @0
    simpr2l
    #
    @38
    @29
    @15
    @3
    @6
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
    @29
    cC
    cU
    @14
    @12
    cV
    @3
    @6
    setccat.c
    @32
    @27
    @35
    @40
    elsetchom
    mpbid
    #
    setcco
    @29
    @41
    @39
    @14
    wceq
    @42
    @3
    @6
    @14
    fcoi1
    syl
    eqtrd
    @29
    @14
    @11
    @30
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
    @29
    cC
    @20
    cU
    @11
    @14
    cV
    @1
    @3
    @6
    setccat.c
    @32
    @33
    @34
    @35
    @40
    @37
    @42
    setcco
    #
    @29
    @44
    @45
    wcel
    @1
    @6
    @44
    wf
    #
    @29
    @41
    @36
    @47
    @42
    @37
    @1
    @3
    @6
    @14
    @11
    fco
    syl2anc
    #
    @29
    cC
    cU
    @44
    @12
    cV
    @1
    @6
    setccat.c
    @32
    @27
    @34
    @40
    elsetchom
    mpbird
    eqeltrd
    @29
    @16
    @14
    ccom
    #
    @11
    @30
    @8
    @20
    co
    #
    co
    #
    @16
    @44
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
    @50
    co
    @16
    @43
    @52
    co
    @29
    @49
    @11
    ccom
    @16
    @44
    ccom
    @51
    @53
    @16
    @14
    @11
    coass
    @29
    cC
    @20
    cU
    @11
    @49
    cV
    @1
    @3
    @8
    setccat.c
    @32
    @33
    @34
    @35
    @7
    @9
    @5
    @18
    @0
    simpr2r
    #
    @37
    @29
    @6
    @8
    @16
    wf
    #
    @41
    @3
    @8
    @49
    wf
    @29
    @17
    @56
    @13
    @15
    @17
    @5
    @10
    @0
    simpr33
    @29
    cC
    cU
    @16
    @12
    cV
    @6
    @8
    setccat.c
    @32
    @27
    @40
    @55
    elsetchom
    mpbid
    #
    @42
    @3
    @6
    @8
    @16
    @14
    fco
    syl2anc
    setcco
    @29
    cC
    @20
    cU
    @44
    @16
    cV
    @1
    @6
    @8
    setccat.c
    @32
    @33
    @34
    @40
    @55
    @48
    @57
    setcco
    3eqtr4a
    @29
    @54
    @49
    @11
    @50
    @29
    cC
    @20
    cU
    @14
    @16
    cV
    @3
    @6
    @8
    setccat.c
    @32
    @33
    @35
    @40
    @55
    @42
    @57
    setcco
    oveq1d
    @29
    @43
    @44
    @16
    @52
    @46
    oveq2d
    3eqtr4d
    iscatd2
end
