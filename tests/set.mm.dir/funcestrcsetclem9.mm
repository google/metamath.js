include "wcel.mm"
include "w3a.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "cbs.mm"
include "cmap.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "wi.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "3ad2ant2.mm"
include "estrchom.mm"
include "3ad2ant3.mm"
include "anbi12d.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "elmapi.mm"
include "fco.mm"
include "syl2an.mm"
include "fvex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ancoms.mm"
include "adantl.mm"
include "fvresi.mm"
include "syl.mm"
include "funcestrcsetclem5.mm"
include "3adantr2.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "estrcco.mm"
include "fveq12d.mm"
include "funcestrcsetclem2.mm"
include "3ad2antr1.mm"
include "3ad2antr2.mm"
include "3ad2antr3.mm"
include "wb.mm"
include "funcestrcsetclem1.mm"
include "feq23d.mm"
include "mpbird.mm"
include "simpll.mm"
include "3simpa.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "funcestrcsetclem6.mm"
include "syl3anc.mm"
include "feq1d.mm"
include "3simpc.mm"
include "simprr.mm"
include "setcco.mm"
include "coeq12d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"

theorem funcestrcsetclem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint ph y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  assert |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( H e. ( X ( Hom ` E ) Y ) /\ K e. ( Y ( Hom ` E ) Z ) ) ) -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` E ) Z ) H ) ) = ( ( ( Y G Z ) ` K ) ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) ) ( ( X G Y ) ` H ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cH
    cX
    cY
    cE
    chom
    cfv
    #
    co
    #
    wcel
    #
    cK
    cY
    cZ
    @4
    co
    #
    wcel
    #
    wa
    #
    cK
    cH
    cX
    cY
    cop
    cZ
    cE
    cco
    cfv
    #
    co
    co
    #
    cX
    cZ
    cG
    co
    #
    cfv
    #
    cK
    cY
    cZ
    cG
    co
    cfv
    #
    cH
    cX
    cY
    cG
    co
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cop
    cZ
    cF
    cfv
    #
    cS
    cco
    cfv
    #
    co
    co
    #
    wceq
    #
    wph
    @3
    wa
    #
    @9
    cH
    cY
    cbs
    cfv
    #
    cX
    cbs
    cfv
    #
    cmap
    co
    #
    wcel
    #
    cK
    cZ
    cbs
    cfv
    #
    @23
    cmap
    co
    #
    wcel
    #
    wa
    #
    @21
    @22
    @6
    @26
    @8
    @29
    @22
    @5
    @25
    cH
    @22
    @24
    @23
    cE
    cU
    @4
    cwun
    cX
    cY
    funcestrcsetc.e
    wph
    cU
    cwun
    wcel
    #
    @3
    funcestrcsetc.u
    adantr
    #
    @4
    eqid
    #
    @3
    wph
    cX
    cU
    wcel
    #
    @0
    @1
    wph
    @34
    wi
    @2
    wph
    @0
    @34
    wph
    cB
    cU
    cX
    wph
    cU
    cE
    cbs
    cfv
    cB
    wph
    cE
    cU
    cwun
    funcestrcsetc.e
    funcestrcsetc.u
    estrcbas
    funcestrcsetc.b
    syl6reqr
    #
    eleq2d
    biimpcd
    3ad2ant1
    impcom
    #
    @3
    wph
    cY
    cU
    wcel
    #
    @1
    @0
    wph
    @37
    wi
    @2
    wph
    @1
    @37
    wph
    cB
    cU
    cY
    @35
    eleq2d
    biimpcd
    3ad2ant2
    impcom
    #
    @24
    eqid
    #
    @23
    eqid
    #
    estrchom
    eleq2d
    @22
    @7
    @28
    cK
    @22
    @23
    @27
    cE
    cU
    @4
    cwun
    cY
    cZ
    funcestrcsetc.e
    @32
    @33
    @38
    @3
    wph
    cZ
    cU
    wcel
    #
    @2
    @0
    wph
    @41
    wi
    @1
    wph
    @2
    @41
    wph
    cB
    cU
    cZ
    @35
    eleq2d
    biimpcd
    3ad2ant3
    impcom
    #
    @40
    @27
    eqid
    #
    estrchom
    eleq2d
    anbi12d
    @22
    @30
    @21
    @22
    @30
    wa
    #
    cK
    cH
    ccom
    #
    cid
    @27
    @24
    cmap
    co
    #
    cres
    #
    cfv
    #
    @45
    @13
    @20
    @44
    @45
    @46
    wcel
    #
    @48
    @45
    wceq
    @30
    @49
    @22
    @29
    @26
    @49
    @29
    @26
    wa
    @24
    @27
    @45
    wf
    #
    @49
    @29
    @23
    @27
    cK
    wf
    #
    @24
    @23
    cH
    wf
    #
    @50
    @26
    cK
    @27
    @23
    elmapi
    #
    cH
    @23
    @24
    elmapi
    #
    @24
    @23
    @27
    cK
    cH
    fco
    syl2an
    @27
    @24
    @45
    cZ
    cbs
    fvex
    cX
    cbs
    fvex
    elmap
    sylibr
    ancoms
    adantl
    @46
    @45
    fvresi
    syl
    @44
    @11
    @45
    @12
    @47
    @22
    @12
    @47
    wceq
    #
    @30
    wph
    @0
    @2
    @55
    @1
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    @24
    @27
    cX
    cZ
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @39
    @43
    funcestrcsetclem5
    3adantr2
    adantr
    @44
    @24
    @23
    cE
    @27
    @10
    cU
    cH
    cK
    cwun
    cX
    cY
    cZ
    funcestrcsetc.e
    @22
    @31
    @30
    @32
    adantr
    #
    @10
    eqid
    @22
    @34
    @30
    @36
    adantr
    @22
    @37
    @30
    @38
    adantr
    @22
    @41
    @30
    @42
    adantr
    @39
    @40
    @43
    @26
    @52
    @22
    @29
    @54
    ad2antrl
    #
    @29
    @51
    @22
    @26
    @53
    ad2antll
    #
    estrcco
    fveq12d
    @44
    @20
    @14
    @15
    ccom
    @45
    @44
    cS
    @19
    cU
    @15
    @14
    cwun
    @16
    @17
    @18
    funcestrcsetc.s
    @56
    @19
    eqid
    @22
    @16
    cU
    wcel
    #
    @30
    wph
    @1
    @0
    @59
    @2
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    3ad2antr1
    adantr
    @22
    @17
    cU
    wcel
    #
    @30
    wph
    @0
    @1
    @60
    @2
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    3ad2antr2
    adantr
    @22
    @18
    cU
    wcel
    #
    @30
    wph
    @0
    @2
    @61
    @1
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cZ
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    3ad2antr3
    adantr
    @44
    @16
    @17
    @15
    wf
    @16
    @17
    cH
    wf
    #
    @44
    @62
    @52
    @57
    @22
    @62
    @52
    wb
    @30
    @22
    @16
    @17
    @24
    @23
    cH
    wph
    @1
    @0
    @16
    @24
    wceq
    @2
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    3ad2antr1
    wph
    @0
    @1
    @17
    @23
    wceq
    @2
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    3ad2antr2
    #
    feq23d
    adantr
    mpbird
    @44
    @16
    @17
    @15
    cH
    @44
    wph
    @0
    @1
    wa
    #
    @26
    @15
    cH
    wceq
    wph
    @3
    @30
    simpll
    #
    @3
    @64
    wph
    @30
    @0
    @1
    @2
    3simpa
    ad2antlr
    @22
    @26
    @29
    simprl
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    cH
    @24
    @23
    cX
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @39
    @40
    funcestrcsetclem6
    syl3anc
    #
    feq1d
    mpbird
    @44
    @17
    @18
    @14
    wf
    @17
    @18
    cK
    wf
    #
    @44
    @67
    @51
    @58
    @22
    @67
    @51
    wb
    @30
    @22
    @17
    @18
    @23
    @27
    cK
    @63
    wph
    @0
    @2
    @18
    @27
    wceq
    @1
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cZ
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    3ad2antr3
    feq23d
    adantr
    mpbird
    @44
    @17
    @18
    @14
    cK
    @44
    wph
    @1
    @2
    wa
    #
    @29
    @14
    cK
    wceq
    @65
    @3
    @68
    wph
    @30
    @0
    @1
    @2
    3simpc
    ad2antlr
    @22
    @26
    @29
    simprr
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    cK
    @23
    @27
    cY
    cZ
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @40
    @43
    funcestrcsetclem6
    syl3anc
    #
    feq1d
    mpbird
    setcco
    @44
    @14
    cK
    @15
    cH
    @69
    @66
    coeq12d
    eqtrd
    3eqtr4d
    ex
    sylbid
    3impia
end
