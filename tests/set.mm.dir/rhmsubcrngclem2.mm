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
include "ad2antrr.mm"
include "simpr.mm"
include "adantr.mm"
include "simprr.mm"
include "rhmresel.mm"
include "syl3anc.mm"
include "anim12i.mm"
include "simprl.mm"
include "rhmco.mm"
include "syl2anc.mm"
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
include "cbs.mm"
include "wf.mm"
include "anim1i.mm"
include "ancoms.mm"
include "rhmf.mm"
include "syl.mm"
include "exp31.mm"
include "3expa.mm"
include "ex.mm"
include "adantlr.mm"
include "rngcco.mm"
include "wceq.mm"
include "cxp.mm"
include "cres.mm"
include "oveqdr.mm"
include "ovres.mm"
include "ad2ant2l.mm"
include "eqtrd.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"

theorem rhmsubcrngclem2
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
  assume rhmsubcrngc.c: |- C = ( RngCat ` U )
  assume rhmsubcrngc.u: |- ( ph -> U e. V )
  assume rhmsubcrngc.b: |- ( ph -> B = ( Ring i^i U ) )
  assume rhmsubcrngc.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )

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
    @2
    wph
    @15
    @19
    wph
    @1
    simpl
    ad2antrr
    #
    @16
    @15
    @19
    @2
    @15
    simpr
    adantr
    @16
    @17
    @18
    simprr
    wph
    cB
    @3
    cH
    @5
    @6
    rhmsubcrngc.h
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
    rhmsubcrngc.h
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
    cC
    @7
    cU
    @4
    @3
    cV
    @0
    @5
    @6
    rhmsubcrngc.c
    @2
    cU
    cV
    wcel
    #
    @15
    @19
    wph
    @30
    @1
    rhmsubcrngc.u
    adantr
    ad2antrr
    @7
    eqid
    @2
    @0
    cU
    wcel
    #
    @15
    @19
    wph
    @1
    @31
    wph
    @1
    @0
    crg
    cU
    cin
    #
    wcel
    @31
    wph
    cB
    @32
    @0
    rhmsubcrngc.b
    eleq2d
    @0
    crg
    cU
    elinel2
    syl6bi
    imp
    ad2antrr
    @16
    @5
    cU
    wcel
    #
    @19
    @15
    @2
    @33
    @13
    @2
    @33
    wi
    @14
    @2
    @13
    @33
    wph
    @13
    @33
    wi
    @1
    wph
    @13
    @5
    @32
    wcel
    @33
    wph
    cB
    @32
    @5
    rhmsubcrngc.b
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
    @34
    @2
    @14
    @34
    @13
    wph
    @14
    @34
    wi
    @1
    wph
    @14
    @6
    @32
    wcel
    @34
    wph
    cB
    @32
    @6
    rhmsubcrngc.b
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
    @19
    @16
    @0
    cbs
    cfv
    #
    @5
    cbs
    cfv
    #
    @4
    wf
    #
    @17
    @16
    @37
    wi
    @18
    @16
    @17
    @37
    @15
    @2
    @17
    @37
    wi
    #
    @13
    @2
    @38
    wi
    @14
    @13
    @2
    @17
    @37
    @13
    @2
    wa
    #
    @17
    wa
    #
    @24
    @37
    @40
    wph
    @27
    @17
    @24
    @39
    wph
    @17
    @13
    wph
    @1
    simprl
    adantr
    @39
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
    @39
    @17
    simpr
    @29
    syl3anc
    @35
    @36
    @0
    @5
    @4
    @35
    eqid
    @36
    eqid
    #
    rhmf
    syl
    exp31
    adantr
    impcom
    com12
    adantr
    impcom
    @16
    @19
    @36
    @6
    cbs
    cfv
    #
    @3
    wf
    #
    @16
    @18
    @43
    @17
    wph
    @15
    @18
    @43
    wi
    @1
    wph
    @15
    wa
    #
    @18
    @43
    @44
    @18
    wa
    @23
    @43
    wph
    @15
    @18
    @23
    @26
    3expa
    @36
    @42
    @5
    @6
    @3
    @41
    @42
    eqid
    rhmf
    syl
    ex
    adantlr
    adantld
    imp
    rngcco
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
    @45
    wph
    cH
    @45
    wceq
    @1
    rhmsubcrngc.h
    adantr
    oveqdr
    @1
    @14
    @46
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
