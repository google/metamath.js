include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "ccom.mm"
include "crh.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "rhmresel.mm"
include "syl3anc.mm"
include "anim12i.mm"
include "simprl.mm"
include "rhmco.mm"
include "syl2anc.mm"
include "cbs.mm"
include "ad3antrrr.mm"
include "eqid.mm"
include "crg.mm"
include "cin.mm"
include "eleq2d.mm"
include "elinel2.mm"
include "syl6bi.mm"
include "imp.mm"
include "wi.mm"
include "com12.mm"
include "impcom.mm"
include "adantld.mm"
include "wf.mm"
include "anim1i.mm"
include "ancoms.mm"
include "rhmf.mm"
include "syl.mm"
include "ex.mm"
include "3expa.mm"
include "adantlr.mm"
include "estrcco.mm"
include "wceq.mm"
include "cxp.mm"
include "cres.mm"
include "oveqdr.mm"
include "ovres.mm"
include "ad2ant2l.mm"
include "eqtrd.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"

theorem rhmsubcsetclem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cV: class V
  let vk: setvar k
  assume rhmsubcsetc.c: |- C = ( ExtStrCat ` U )
  assume rhmsubcsetc.u: |- ( ph -> U e. V )
  assume rhmsubcsetc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcsetc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )

  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint U x
  disjoint U y
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ( ph /\ x e. B ) -> A. y e. B A. z e. B A. f e. ( x H y ) A. g e. ( y H z ) ( g ( <. x , y >. ( comp ` C ) z ) f ) e. ( x H z ) )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    vg
    cv
    #
    vf
    cv
    #
    @0
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    @0
    @6
    cH
    co
    #
    wcel
    #
    vg
    @5
    @6
    cH
    co
    #
    wral
    vf
    @0
    @5
    cH
    co
    #
    wral
    vy
    vz
    cB
    cB
    @2
    @5
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    @10
    vf
    vg
    @12
    @11
    @16
    @4
    @12
    wcel
    #
    @3
    @11
    wcel
    #
    wa
    #
    wa
    #
    @3
    @4
    ccom
    #
    @0
    @6
    crh
    co
    #
    @8
    @9
    @20
    @3
    @5
    @6
    crh
    co
    wcel
    #
    @4
    @0
    @5
    crh
    co
    wcel
    #
    @21
    @22
    wcel
    @20
    wph
    @15
    @18
    @23
    @16
    wph
    @19
    @2
    wph
    @15
    wph
    @1
    simpl
    adantr
    adantr
    #
    @16
    @15
    @19
    @2
    @15
    simpr
    adantr
    @19
    @18
    @16
    @17
    @18
    simpr
    adantl
    wph
    cB
    @3
    cH
    @5
    @6
    rhmsubcsetc.h
    rhmresel
    #
    syl3anc
    @20
    wph
    @1
    @13
    wa
    #
    @17
    @24
    @25
    @16
    @27
    @19
    @2
    @1
    @15
    @13
    wph
    @1
    simpr
    #
    @13
    @14
    simpl
    anim12i
    adantr
    @16
    @17
    @18
    simprl
    wph
    cB
    @4
    cH
    @0
    @5
    rhmsubcsetc.h
    rhmresel
    #
    syl3anc
    @0
    @5
    @6
    @3
    @4
    rhmco
    syl2anc
    @20
    @0
    cbs
    cfv
    #
    @5
    cbs
    cfv
    #
    cC
    @6
    cbs
    cfv
    #
    @7
    cU
    @4
    @3
    cV
    @0
    @5
    @6
    rhmsubcsetc.c
    wph
    cU
    cV
    wcel
    @1
    @15
    @19
    rhmsubcsetc.u
    ad3antrrr
    @7
    eqid
    @16
    @0
    cU
    wcel
    #
    @19
    @2
    @33
    @15
    wph
    @1
    @33
    wph
    @1
    @0
    crg
    cU
    cin
    #
    wcel
    @33
    wph
    cB
    @34
    @0
    rhmsubcsetc.b
    eleq2d
    @0
    crg
    cU
    elinel2
    syl6bi
    imp
    adantr
    adantr
    @16
    @5
    cU
    wcel
    #
    @19
    @15
    @2
    @35
    @13
    @2
    @35
    wi
    @14
    @2
    @13
    @35
    wph
    @13
    @35
    wi
    @1
    wph
    @13
    @5
    @34
    wcel
    @35
    wph
    cB
    @34
    @5
    rhmsubcsetc.b
    eleq2d
    @5
    crg
    cU
    elinel2
    syl6bi
    adantr
    com12
    adantr
    impcom
    adantr
    @16
    @6
    cU
    wcel
    #
    @19
    @2
    @15
    @36
    @2
    @14
    @36
    @13
    wph
    @14
    @36
    wi
    @1
    wph
    @14
    @6
    @34
    wcel
    @36
    wph
    cB
    @34
    @6
    rhmsubcsetc.b
    eleq2d
    @6
    crg
    cU
    elinel2
    syl6bi
    adantr
    adantld
    imp
    adantr
    @30
    eqid
    #
    @31
    eqid
    #
    @32
    eqid
    #
    @19
    @16
    @30
    @31
    @4
    wf
    #
    @17
    @16
    @40
    wi
    @18
    @16
    @17
    @40
    @15
    @2
    @17
    @40
    wi
    #
    @13
    @2
    @41
    wi
    @14
    @13
    @2
    @41
    @13
    @2
    wa
    #
    @17
    @40
    @42
    @17
    wa
    #
    @24
    @40
    @43
    wph
    @27
    @17
    @24
    @42
    wph
    @17
    @13
    wph
    @1
    simprl
    adantr
    @42
    @27
    @17
    @2
    @13
    @27
    @2
    @1
    @13
    @28
    anim1i
    ancoms
    adantr
    @42
    @17
    simpr
    @29
    syl3anc
    @30
    @31
    @0
    @5
    @4
    @37
    @38
    rhmf
    syl
    ex
    ex
    adantr
    impcom
    com12
    adantr
    impcom
    @16
    @19
    @31
    @32
    @3
    wf
    #
    @16
    @18
    @44
    @17
    wph
    @15
    @18
    @44
    wi
    @1
    wph
    @15
    wa
    #
    @18
    @44
    @45
    @18
    wa
    @23
    @44
    wph
    @15
    @18
    @23
    @26
    3expa
    @31
    @32
    @5
    @6
    @3
    @38
    @39
    rhmf
    syl
    ex
    adantlr
    adantld
    imp
    estrcco
    @16
    @9
    @22
    wceq
    @19
    @16
    @9
    @0
    @6
    crh
    cB
    cB
    cxp
    cres
    #
    co
    #
    @22
    @2
    @15
    vx
    vz
    cH
    @46
    wph
    cH
    @46
    wceq
    @1
    rhmsubcsetc.h
    adantr
    oveqdr
    @1
    @14
    @47
    @22
    wceq
    wph
    @13
    @0
    @6
    cB
    cB
    crh
    ovres
    ad2ant2l
    eqtrd
    adantr
    3eltr4d
    ralrimivva
    ralrimivva
end
