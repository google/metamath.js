include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "w3a.mm"
include "cco.mm"
include "cidfu.mm"
include "cvv.mm"
include "cbs.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "ccatc.mm"
include "fvex.mm"
include "eqeltri.mm"
include "biid.mm"
include "cfunc.mm"
include "ccat.mm"
include "cin.mm"
include "id.mm"
include "catcbas.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "eqid.mm"
include "idfucl.mm"
include "syl.mm"
include "simpl.mm"
include "simpr.mm"
include "catchom.mm"
include "eleqtrrd.mm"
include "cop.mm"
include "ccofu.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "simpr31.mm"
include "eleqtrd.mm"
include "syldan.mm"
include "catcco.mm"
include "cofulid.mm"
include "eqtrd.mm"
include "simpr2l.mm"
include "simpr32.mm"
include "cofurid.mm"
include "cofucl.mm"
include "3eltr4d.mm"
include "simpr33.mm"
include "simpr2r.mm"
include "cofuass.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "iscatd2.mm"

theorem catccatid
  let vx: setvar x
  let cB: class B
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
  assume catccatid.c: |- C = ( CatCat ` U )
  assume catccatid.b: |- B = ( Base ` C )

  disjoint B x
  disjoint C x
  disjoint U x
  disjoint V x
  disjoint f g
  disjoint f h
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint U f
  disjoint U g
  disjoint U h
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint ph x
  disjoint V f
  disjoint V g
  disjoint V h
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint X x
  assert |- ( U e. V -> ( C e. Cat /\ ( Id ` C ) = ( x e. B |-> ( idFunc ` x ) ) ) )

  proof
    cU
    cV
    wcel
    #
    vw
    cv
    #
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    cB
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
    #
    wcel
    #
    vg
    cv
    #
    @3
    @6
    @12
    co
    #
    wcel
    #
    vh
    cv
    #
    @6
    @8
    @12
    co
    #
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
    cB
    cC
    cC
    cco
    cfv
    #
    @3
    cidfu
    cfv
    #
    vf
    vg
    vh
    @12
    cvv
    cB
    cC
    cbs
    cfv
    wceq
    @0
    catccatid.b
    a1i
    @0
    @12
    eqidd
    @0
    @23
    eqidd
    cC
    cvv
    wcel
    @0
    cC
    cU
    ccatc
    cfv
    cvv
    catccatid.c
    cU
    ccatc
    fvex
    eqeltri
    a1i
    @22
    biid
    @0
    @4
    wa
    #
    @24
    @3
    @3
    cfunc
    co
    #
    @3
    @3
    @12
    co
    @25
    @3
    ccat
    wcel
    @24
    @26
    wcel
    #
    @0
    cB
    ccat
    @3
    @0
    cB
    cU
    ccat
    cin
    ccat
    @0
    cB
    cC
    cU
    cV
    catccatid.c
    catccatid.b
    @0
    id
    catcbas
    cU
    ccat
    inss2
    syl6eqss
    sselda
    @3
    @24
    @24
    eqid
    #
    idfucl
    syl
    #
    @25
    cB
    cC
    cU
    @12
    cV
    @3
    @3
    catccatid.c
    catccatid.b
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
    @31
    catchom
    eleqtrrd
    @0
    @22
    wa
    #
    @24
    @11
    @1
    @3
    cop
    #
    @3
    @23
    co
    co
    @24
    @11
    ccofu
    co
    @11
    @32
    cB
    cC
    @23
    cU
    @11
    @24
    cV
    @1
    @3
    @3
    catccatid.c
    catccatid.b
    @0
    @22
    simpl
    #
    @23
    eqid
    #
    @2
    @4
    @10
    @21
    @0
    simpr1l
    #
    @2
    @4
    @10
    @21
    @0
    simpr1r
    #
    @37
    @32
    @11
    @13
    @1
    @3
    cfunc
    co
    @14
    @17
    @20
    @5
    @10
    @0
    simpr31
    @32
    cB
    cC
    cU
    @12
    cV
    @1
    @3
    catccatid.c
    catccatid.b
    @34
    @30
    @36
    @37
    catchom
    eleqtrd
    #
    @0
    @22
    @4
    @27
    @37
    @29
    syldan
    #
    catcco
    @32
    @1
    @3
    @11
    @24
    @38
    @28
    cofulid
    eqtrd
    @32
    @15
    @24
    @3
    @3
    cop
    @6
    @23
    co
    co
    @15
    @24
    ccofu
    co
    @15
    @32
    cB
    cC
    @23
    cU
    @24
    @15
    cV
    @3
    @3
    @6
    catccatid.c
    catccatid.b
    @34
    @35
    @37
    @37
    @7
    @9
    @5
    @21
    @0
    simpr2l
    #
    @39
    @32
    @15
    @16
    @3
    @6
    cfunc
    co
    @14
    @17
    @20
    @5
    @10
    @0
    simpr32
    @32
    cB
    cC
    cU
    @12
    cV
    @3
    @6
    catccatid.c
    catccatid.b
    @34
    @30
    @37
    @40
    catchom
    eleqtrd
    #
    catcco
    @32
    @3
    @6
    @15
    @24
    @41
    @28
    cofurid
    eqtrd
    @32
    @15
    @11
    ccofu
    co
    #
    @1
    @6
    cfunc
    co
    @15
    @11
    @33
    @6
    @23
    co
    co
    #
    @1
    @6
    @12
    co
    @32
    @1
    @3
    @6
    @11
    @15
    @38
    @41
    cofucl
    #
    @32
    cB
    cC
    @23
    cU
    @11
    @15
    cV
    @1
    @3
    @6
    catccatid.c
    catccatid.b
    @34
    @35
    @36
    @37
    @40
    @38
    @41
    catcco
    #
    @32
    cB
    cC
    cU
    @12
    cV
    @1
    @6
    catccatid.c
    catccatid.b
    @34
    @30
    @36
    @40
    catchom
    3eltr4d
    @32
    @18
    @15
    ccofu
    co
    #
    @11
    @33
    @8
    @23
    co
    #
    co
    #
    @18
    @42
    @1
    @6
    cop
    @8
    @23
    co
    #
    co
    #
    @18
    @15
    @3
    @6
    cop
    @8
    @23
    co
    co
    #
    @11
    @47
    co
    @18
    @43
    @49
    co
    @32
    @46
    @11
    ccofu
    co
    @18
    @42
    ccofu
    co
    @48
    @50
    @32
    @1
    @3
    @6
    @8
    @11
    @15
    @18
    @38
    @41
    @32
    @18
    @19
    @6
    @8
    cfunc
    co
    @14
    @17
    @20
    @5
    @10
    @0
    simpr33
    @32
    cB
    cC
    cU
    @12
    cV
    @6
    @8
    catccatid.c
    catccatid.b
    @34
    @30
    @40
    @7
    @9
    @5
    @21
    @0
    simpr2r
    #
    catchom
    eleqtrd
    #
    cofuass
    @32
    cB
    cC
    @23
    cU
    @11
    @46
    cV
    @1
    @3
    @8
    catccatid.c
    catccatid.b
    @34
    @35
    @36
    @37
    @52
    @38
    @32
    @3
    @6
    @8
    @15
    @18
    @41
    @53
    cofucl
    catcco
    @32
    cB
    cC
    @23
    cU
    @42
    @18
    cV
    @1
    @6
    @8
    catccatid.c
    catccatid.b
    @34
    @35
    @36
    @40
    @52
    @44
    @53
    catcco
    3eqtr4d
    @32
    @51
    @46
    @11
    @47
    @32
    cB
    cC
    @23
    cU
    @15
    @18
    cV
    @3
    @6
    @8
    catccatid.c
    catccatid.b
    @34
    @35
    @37
    @40
    @52
    @41
    @53
    catcco
    oveq1d
    @32
    @43
    @42
    @18
    @49
    @45
    oveq2d
    3eqtr4d
    iscatd2
end
