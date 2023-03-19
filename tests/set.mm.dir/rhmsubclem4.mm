include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccom.mm"
include "crh.mm"
include "cop.mm"
include "crngc.mm"
include "cfv.mm"
include "cco.mm"
include "wceq.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "rhmsubclem2.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rhmco.mm"
include "ancoms.mm"
include "syl6bi.mm"
include "imp.mm"
include "ad3antrrr.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "crg.mm"
include "cin.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "sselda.mm"
include "wi.mm"
include "sseld.mm"
include "adantrd.mm"
include "adantld.mm"
include "cbs.mm"
include "wf.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovresd.mm"
include "syl5eq.mm"
include "eqid.mm"
include "rhmf.mm"
include "com12.mm"
include "impcom.mm"
include "ovres.mm"
include "rngcco.mm"
include "3eltr4d.mm"

theorem rhmsubclem4
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
  assume rngcrescrhm.u: |- ( ph -> U e. V )
  assume rngcrescrhm.c: |- C = ( RngCat ` U )
  assume rngcrescrhm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhm.h: |- H = ( RingHom |` ( R X. R ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint C y
  disjoint U y
  disjoint V y
  disjoint ph y
  disjoint R z
  disjoint x z
  disjoint y z
  disjoint U x
  disjoint ph x
  disjoint k x
  assert |- ( ( ( ( ph /\ x e. R ) /\ ( y e. R /\ z e. R ) ) /\ ( f e. ( x H y ) /\ g e. ( y H z ) ) ) -> ( g ( <. x , y >. ( comp ` ( RngCat ` U ) ) z ) f ) e. ( x H z ) )

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
    crngc
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
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem2
    syl3anc
    eleq2d
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
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem2
    syl3anc
    eleq2d
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
    cC
    @20
    cU
    @9
    @12
    cV
    @0
    @3
    @5
    rngcrescrhm.c
    wph
    cU
    cV
    wcel
    @1
    @7
    @15
    rngcrescrhm.u
    ad3antrrr
    @19
    cC
    cco
    cC
    @19
    rngcrescrhm.c
    eqcomi
    fveq2i
    @8
    @0
    cU
    wcel
    #
    @15
    @2
    @31
    @7
    wph
    cR
    cU
    @0
    wph
    cR
    crg
    cU
    cin
    cU
    rngcrescrhm.r
    crg
    cU
    inss2
    syl6eqss
    #
    sselda
    adantr
    adantr
    @8
    @3
    cU
    wcel
    #
    @15
    @2
    @7
    @33
    wph
    @7
    @33
    wi
    @1
    wph
    @4
    @33
    @6
    wph
    cR
    cU
    @3
    @32
    sseld
    adantrd
    adantr
    imp
    adantr
    @8
    @5
    cU
    wcel
    #
    @15
    @2
    @7
    @34
    wph
    @7
    @34
    wi
    @1
    wph
    @6
    @34
    @4
    wph
    cR
    cU
    @5
    @32
    sseld
    adantld
    adantr
    imp
    adantr
    @15
    @8
    @0
    cbs
    cfv
    #
    @3
    cbs
    cfv
    #
    @9
    wf
    #
    @11
    @8
    @37
    wi
    @14
    @8
    @11
    @37
    @8
    @11
    @24
    @37
    @8
    @10
    @23
    @9
    @8
    @10
    @0
    @3
    crh
    cR
    cR
    cxp
    cres
    #
    co
    @23
    cH
    @38
    @0
    @3
    rngcrescrhm.h
    oveqi
    @8
    @0
    @3
    crh
    cR
    @28
    @29
    ovresd
    syl5eq
    eleq2d
    @35
    @36
    @0
    @3
    @9
    @35
    eqid
    @36
    eqid
    #
    rhmf
    syl6bi
    com12
    adantr
    impcom
    @15
    @8
    @36
    @5
    cbs
    cfv
    #
    @12
    wf
    #
    @14
    @8
    @41
    wi
    @11
    @8
    @14
    @41
    @8
    @14
    @26
    @41
    @8
    @13
    @25
    @12
    @8
    @13
    @3
    @5
    @38
    co
    #
    @25
    cH
    @38
    @3
    @5
    rngcrescrhm.h
    oveqi
    @7
    @42
    @25
    wceq
    @2
    @3
    @5
    cR
    cR
    crh
    ovres
    adantl
    syl5eq
    eleq2d
    @36
    @40
    @3
    @5
    @12
    @39
    @40
    eqid
    rhmf
    syl6bi
    com12
    adantl
    impcom
    rngcco
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
    @43
    @27
    @28
    @30
    wph
    cC
    cR
    cU
    cH
    cV
    @0
    @5
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubclem2
    syl3anc
    adantr
    3eltr4d
end
