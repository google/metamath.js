include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccom.mm"
include "crh.mm"
include "cop.mm"
include "crngcALTV.mm"
include "cfv.mm"
include "cco.mm"
include "wceq.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "rhmsubcALTVlem2.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rhmco.mm"
include "ancoms.mm"
include "syl6bi.mm"
include "imp.mm"
include "cbs.mm"
include "eqid.mm"
include "ad3antrrr.mm"
include "crg.mm"
include "cin.mm"
include "crng.mm"
include "incom.mm"
include "wss.mm"
include "wi.mm"
include "ringrng.mm"
include "a1i.mm"
include "ssrdv.mm"
include "sslin.mm"
include "syl.mm"
include "syl5eqss.mm"
include "rngcbasALTV.mm"
include "3sstr4d.mm"
include "sselda.mm"
include "sseld.mm"
include "com12.mm"
include "impcom.mm"
include "adantld.mm"
include "crngh.mm"
include "rhmisrnghm.mm"
include "rngccoALTV.mm"
include "3eltr4d.mm"

theorem rhmsubcALTVlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cR: class R
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cV: class V
  let vk: setvar k
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint U y
  disjoint V y
  disjoint ph y
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint k x
  assert |- ( ( ( ( ph /\ x e. R ) /\ ( y e. R /\ z e. R ) ) /\ ( f e. ( x H y ) /\ g e. ( y H z ) ) ) -> ( g ( <. x , y >. ( comp ` ( RngCatALTV ` U ) ) z ) f ) e. ( x H z ) )

  proof
    wph
    vx
    cv
    #
    cR
    wcel
    #
    wa
    #
    vy
    cv
    #
    cR
    wcel
    #
    vz
    cv
    #
    cR
    wcel
    #
    wa
    #
    wa
    #
    vf
    cv
    #
    @0
    @3
    cH
    co
    #
    wcel
    #
    vg
    cv
    #
    @3
    @5
    cH
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    @12
    @9
    ccom
    #
    @0
    @5
    crh
    co
    #
    @12
    @9
    @0
    @3
    cop
    @5
    cU
    crngcALTV
    cfv
    #
    cco
    cfv
    #
    co
    co
    @0
    @5
    cH
    co
    #
    @8
    @15
    @17
    @18
    wcel
    #
    @8
    @15
    @9
    @0
    @3
    crh
    co
    #
    wcel
    #
    @12
    @3
    @5
    crh
    co
    #
    wcel
    #
    wa
    @22
    @8
    @11
    @24
    @14
    @26
    @8
    @10
    @23
    @9
    @8
    wph
    @1
    @4
    @10
    @23
    wceq
    @2
    wph
    @7
    wph
    @1
    simpl
    adantr
    #
    @2
    @1
    @7
    wph
    @1
    simpr
    adantr
    #
    @7
    @4
    @2
    @4
    @6
    simpl
    adantl
    #
    wph
    cC
    cR
    cU
    cH
    cV
    @0
    @3
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem2
    syl3anc
    eleq2d
    #
    @8
    @13
    @25
    @12
    @8
    wph
    @4
    @6
    @13
    @25
    wceq
    @27
    @29
    @7
    @6
    @2
    @4
    @6
    simpr
    adantl
    #
    wph
    cC
    cR
    cU
    cH
    cV
    @3
    @5
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem2
    syl3anc
    eleq2d
    #
    anbi12d
    @26
    @24
    @22
    @0
    @3
    @5
    @12
    @9
    rhmco
    ancoms
    syl6bi
    imp
    @16
    @19
    cbs
    cfv
    #
    @19
    @20
    cU
    @9
    @12
    cV
    @0
    @3
    @5
    @19
    eqid
    #
    @33
    eqid
    #
    wph
    cU
    cV
    wcel
    @1
    @7
    @15
    rngcrescrhmALTV.u
    ad3antrrr
    @20
    eqid
    @8
    @0
    @33
    wcel
    #
    @15
    @2
    @36
    @7
    wph
    cR
    @33
    @0
    wph
    crg
    cU
    cin
    #
    cU
    crng
    cin
    #
    cR
    @33
    wph
    @37
    cU
    crg
    cin
    #
    @38
    crg
    cU
    incom
    wph
    crg
    crng
    wss
    @39
    @38
    wss
    wph
    vx
    crg
    crng
    @0
    crg
    wcel
    @0
    crng
    wcel
    wi
    wph
    @0
    ringrng
    a1i
    ssrdv
    crg
    crng
    cU
    sslin
    syl
    syl5eqss
    rngcrescrhmALTV.r
    wph
    @33
    @19
    cU
    cV
    @34
    @35
    rngcrescrhmALTV.u
    rngcbasALTV
    3sstr4d
    #
    sselda
    adantr
    adantr
    @8
    @3
    @33
    wcel
    #
    @15
    @7
    @2
    @41
    @4
    @2
    @41
    wi
    @6
    @2
    @4
    @41
    wph
    @4
    @41
    wi
    @1
    wph
    cR
    @33
    @3
    @40
    sseld
    adantr
    com12
    adantr
    impcom
    adantr
    @8
    @5
    @33
    wcel
    #
    @15
    @2
    @7
    @42
    @2
    @6
    @42
    @4
    wph
    @6
    @42
    wi
    @1
    wph
    cR
    @33
    @5
    @40
    sseld
    adantr
    adantld
    imp
    adantr
    @15
    @8
    @9
    @0
    @3
    crngh
    co
    wcel
    #
    @11
    @8
    @43
    wi
    @14
    @8
    @11
    @43
    @8
    @11
    @24
    @43
    @30
    @0
    @3
    @9
    rhmisrnghm
    syl6bi
    com12
    adantr
    impcom
    @8
    @15
    @12
    @3
    @5
    crngh
    co
    wcel
    #
    @8
    @14
    @44
    @11
    @8
    @14
    @26
    @44
    @32
    @3
    @5
    @12
    rhmisrnghm
    syl6bi
    adantld
    imp
    rngccoALTV
    @8
    @21
    @18
    wceq
    #
    @15
    @8
    wph
    @1
    @6
    @45
    @27
    @28
    @31
    wph
    cC
    cR
    cU
    cH
    cV
    @0
    @5
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTVlem2
    syl3anc
    adantr
    3eltr4d
end
