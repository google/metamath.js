include "wcel.mm"
include "w3a.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "cmap.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "wi.mm"
include "cbs.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "3ad2ant2.mm"
include "setchom.mm"
include "3ad2ant3.mm"
include "anbi12d.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "elmapi.mm"
include "fco.mm"
include "syl2anr.mm"
include "adantl.mm"
include "wb.mm"
include "elmapg.mm"
include "ancoms.mm"
include "3adant2.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "fvresi.mm"
include "syl.mm"
include "funcsetcestrclem5.mm"
include "3adantr2.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "setcco.mm"
include "fveq12d.mm"
include "funcsetcestrclem2.mm"
include "3ad2antr1.mm"
include "3ad2antr2.mm"
include "3ad2antr3.mm"
include "simpll.mm"
include "3simpa.mm"
include "simprl.mm"
include "funcsetcestrclem6.mm"
include "syl3anc.mm"
include "cnx.mm"
include "csn.mm"
include "funcsetcestrclem1.mm"
include "fveq2d.mm"
include "1strbas.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "feq123d.mm"
include "3simpc.mm"
include "simprr.mm"
include "estrcco.mm"
include "coeq12d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"

theorem funcsetcestrclem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrc.g: |- ( ph -> G = ( x e. C , y e. C |-> ( _I |` ( y ^m x ) ) ) )
  assume funcsetcestrc.e: |- E = ( ExtStrCat ` U )

  disjoint C x
  disjoint X x
  disjoint ph x
  disjoint C y
  disjoint x y
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph y
  disjoint Z x
  disjoint Z y
  disjoint C f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  assert |- ( ( ph /\ ( X e. C /\ Y e. C /\ Z e. C ) /\ ( H e. ( X ( Hom ` S ) Y ) /\ K e. ( Y ( Hom ` S ) Z ) ) ) -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` S ) Z ) H ) ) = ( ( ( Y G Z ) ` K ) ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` E ) ( F ` Z ) ) ( ( X G Y ) ` H ) ) )

  proof
    wph
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    cZ
    cC
    wcel
    #
    w3a
    #
    cH
    cX
    cY
    cS
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
    cS
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
    cE
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
    cX
    cmap
    co
    #
    wcel
    #
    cK
    cZ
    cY
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
    @24
    @8
    @26
    @22
    @5
    @23
    cH
    @22
    cS
    cU
    @4
    cwun
    cX
    cY
    funcsetcestrc.s
    wph
    cU
    cwun
    wcel
    #
    @3
    funcsetcestrc.u
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
    @31
    wi
    @2
    wph
    @0
    @31
    wph
    cC
    cU
    cX
    wph
    cU
    cS
    cbs
    cfv
    cC
    wph
    cS
    cU
    cwun
    funcsetcestrc.s
    funcsetcestrc.u
    setcbas
    funcsetcestrc.c
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
    @34
    wi
    @2
    wph
    @1
    @34
    wph
    cC
    cU
    cY
    @32
    eleq2d
    biimpcd
    3ad2ant2
    impcom
    #
    setchom
    eleq2d
    @22
    @7
    @25
    cK
    @22
    cS
    cU
    @4
    cwun
    cY
    cZ
    funcsetcestrc.s
    @29
    @30
    @35
    @3
    wph
    cZ
    cU
    wcel
    #
    @2
    @0
    wph
    @36
    wi
    @1
    wph
    @2
    @36
    wph
    cC
    cU
    cZ
    @32
    eleq2d
    biimpcd
    3ad2ant3
    impcom
    #
    setchom
    eleq2d
    anbi12d
    @22
    @27
    @21
    @22
    @27
    wa
    #
    cK
    cH
    ccom
    #
    cid
    cZ
    cX
    cmap
    co
    #
    cres
    #
    cfv
    #
    @39
    @13
    @20
    @38
    @39
    @40
    wcel
    #
    @42
    @39
    wceq
    @38
    @43
    cX
    cZ
    @39
    wf
    #
    @27
    @44
    @22
    @26
    cY
    cZ
    cK
    wf
    #
    cX
    cY
    cH
    wf
    #
    @44
    @24
    cK
    cZ
    cY
    elmapi
    #
    cH
    cY
    cX
    elmapi
    #
    cX
    cY
    cZ
    cK
    cH
    fco
    syl2anr
    adantl
    @3
    @43
    @44
    wb
    #
    wph
    @27
    @0
    @2
    @49
    @1
    @2
    @0
    @49
    cZ
    cX
    @39
    cC
    cC
    elmapg
    ancoms
    3adant2
    ad2antlr
    mpbird
    @40
    @39
    fvresi
    syl
    @38
    @11
    @39
    @12
    @41
    @22
    @12
    @41
    wceq
    #
    @27
    wph
    @0
    @2
    @50
    @1
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cX
    cZ
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem5
    3adantr2
    adantr
    @38
    cS
    @10
    cU
    cH
    cK
    cwun
    cX
    cY
    cZ
    funcsetcestrc.s
    @22
    @28
    @27
    @29
    adantr
    #
    @10
    eqid
    @22
    @31
    @27
    @33
    adantr
    @22
    @34
    @27
    @35
    adantr
    @22
    @36
    @27
    @37
    adantr
    @24
    @46
    @22
    @26
    @48
    ad2antrl
    #
    @26
    @45
    @22
    @24
    @47
    ad2antll
    #
    setcco
    fveq12d
    @38
    @20
    @14
    @15
    ccom
    @39
    @38
    @16
    cbs
    cfv
    #
    @17
    cbs
    cfv
    #
    cE
    @18
    cbs
    cfv
    #
    @19
    cU
    @15
    @14
    cwun
    @16
    @17
    @18
    funcsetcestrc.e
    @51
    @19
    eqid
    @22
    @16
    cU
    wcel
    #
    @27
    wph
    @1
    @0
    @57
    @2
    wph
    vx
    cC
    cS
    cU
    cF
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem2
    3ad2antr1
    adantr
    @22
    @17
    cU
    wcel
    #
    @27
    wph
    @0
    @1
    @58
    @2
    wph
    vx
    cC
    cS
    cU
    cF
    cY
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem2
    3ad2antr2
    adantr
    @22
    @18
    cU
    wcel
    #
    @27
    wph
    @0
    @2
    @59
    @1
    wph
    vx
    cC
    cS
    cU
    cF
    cZ
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem2
    3ad2antr3
    adantr
    @54
    eqid
    @55
    eqid
    @56
    eqid
    @38
    @54
    @55
    @15
    wf
    @46
    @52
    @38
    @54
    cX
    @55
    cY
    @15
    cH
    @38
    wph
    @0
    @1
    wa
    #
    @24
    @15
    cH
    wceq
    wph
    @3
    @27
    simpll
    #
    @3
    @60
    wph
    @27
    @0
    @1
    @2
    3simpa
    ad2antlr
    @22
    @24
    @26
    simprl
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cH
    cX
    cY
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem6
    syl3anc
    #
    @22
    @54
    cX
    wceq
    @27
    @22
    @54
    cnx
    cbs
    cfv
    #
    cX
    cop
    csn
    #
    cbs
    cfv
    #
    cX
    @22
    @16
    @64
    cbs
    wph
    @1
    @0
    @16
    @64
    wceq
    @2
    wph
    vx
    cC
    cS
    cU
    cF
    cX
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    3ad2antr1
    fveq2d
    @3
    @65
    cX
    wceq
    #
    wph
    @0
    @1
    @66
    @2
    @0
    cX
    @65
    cX
    @64
    cC
    @64
    eqid
    1strbas
    eqcomd
    3ad2ant1
    adantl
    eqtrd
    adantr
    @22
    @55
    cY
    wceq
    @27
    @22
    @55
    @63
    cY
    cop
    csn
    #
    cbs
    cfv
    #
    cY
    @22
    @17
    @67
    cbs
    wph
    @0
    @1
    @17
    @67
    wceq
    @2
    wph
    vx
    cC
    cS
    cU
    cF
    cY
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    3ad2antr2
    fveq2d
    @3
    @68
    cY
    wceq
    #
    wph
    @1
    @0
    @69
    @2
    @1
    cY
    @68
    cY
    @67
    cC
    @67
    eqid
    1strbas
    eqcomd
    3ad2ant2
    adantl
    eqtrd
    adantr
    #
    feq123d
    mpbird
    @38
    @55
    @56
    @14
    wf
    @45
    @53
    @38
    @55
    cY
    @56
    cZ
    @14
    cK
    @38
    wph
    @1
    @2
    wa
    #
    @26
    @14
    cK
    wceq
    @61
    @3
    @71
    wph
    @27
    @0
    @1
    @2
    3simpc
    ad2antlr
    @22
    @24
    @26
    simprr
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cK
    cY
    cZ
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem6
    syl3anc
    #
    @70
    @22
    @56
    cZ
    wceq
    @27
    @22
    @56
    @63
    cZ
    cop
    csn
    #
    cbs
    cfv
    #
    cZ
    @22
    @18
    @73
    cbs
    wph
    @0
    @2
    @18
    @73
    wceq
    @1
    wph
    vx
    cC
    cS
    cU
    cF
    cZ
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    3ad2antr3
    fveq2d
    @3
    @74
    cZ
    wceq
    #
    wph
    @2
    @0
    @75
    @1
    @2
    cZ
    @74
    cZ
    @73
    cC
    @73
    eqid
    1strbas
    eqcomd
    3ad2ant3
    adantl
    eqtrd
    adantr
    feq123d
    mpbird
    estrcco
    @38
    @14
    cK
    @15
    cH
    @72
    @62
    coeq12d
    eqtrd
    3eqtr4d
    ex
    sylbid
    3impia
end
