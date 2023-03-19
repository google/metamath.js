include "wcel.mm"
include "w3a.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "crh.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr1.mm"
include "simpr2.mm"
include "ringchom.mm"
include "eleq2d.mm"
include "simpr3.mm"
include "anbi12d.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "rhmco.mm"
include "ancoms.mm"
include "adantl.mm"
include "fvresi.mm"
include "syl.mm"
include "funcringcsetcALTV2lem5.mm"
include "3adantr2.mm"
include "wi.mm"
include "crg.mm"
include "cin.mm"
include "ringcbas.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "sseld.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "cbs.mm"
include "wf.mm"
include "rhmf.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ringcco.mm"
include "fveq12d.mm"
include "funcringcsetcALTV2lem2.mm"
include "3ad2antr1.mm"
include "3ad2antr2.mm"
include "3ad2antr3.mm"
include "wb.mm"
include "funcringcsetcALTV2lem1.mm"
include "feq23d.mm"
include "mpbird.mm"
include "simpll.mm"
include "3simpa.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "funcringcsetcALTV2lem6.mm"
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

theorem funcringcsetcALTV2lem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  assume funcringcsetcALTV2.r: |- R = ( RingCat ` U )
  assume funcringcsetcALTV2.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV2.b: |- B = ( Base ` R )
  assume funcringcsetcALTV2.c: |- C = ( Base ` S )
  assume funcringcsetcALTV2.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV2.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV2.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph y
  disjoint Z x
  disjoint Z y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  disjoint k x
  assert |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( H e. ( X ( Hom ` R ) Y ) /\ K e. ( Y ( Hom ` R ) Z ) ) ) -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` R ) Z ) H ) ) = ( ( ( Y G Z ) ` K ) ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) ) ( ( X G Y ) ` H ) ) )

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
    cR
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
    cR
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
    cX
    cY
    crh
    co
    #
    wcel
    #
    cK
    cY
    cZ
    crh
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
    cB
    cR
    cU
    @4
    cwun
    cX
    cY
    funcringcsetcALTV2.r
    funcringcsetcALTV2.b
    wph
    cU
    cwun
    wcel
    #
    @3
    funcringcsetcALTV2.u
    adantr
    #
    @4
    eqid
    #
    wph
    @0
    @1
    @2
    simpr1
    wph
    @0
    @1
    @2
    simpr2
    #
    ringchom
    eleq2d
    @22
    @7
    @25
    cK
    @22
    cB
    cR
    cU
    @4
    cwun
    cY
    cZ
    funcringcsetcALTV2.r
    funcringcsetcALTV2.b
    @29
    @30
    @31
    wph
    @0
    @1
    @2
    simpr3
    ringchom
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
    cX
    cZ
    crh
    co
    #
    cres
    #
    cfv
    #
    @33
    @13
    @20
    @32
    @33
    @34
    wcel
    #
    @36
    @33
    wceq
    @27
    @37
    @22
    @26
    @24
    @37
    cX
    cY
    cZ
    cK
    cH
    rhmco
    ancoms
    adantl
    @34
    @33
    fvresi
    syl
    @32
    @11
    @33
    @12
    @35
    @22
    @12
    @35
    wceq
    #
    @27
    wph
    @0
    @2
    @38
    @1
    wph
    vx
    vy
    cB
    cC
    cR
    cS
    cU
    cF
    cG
    cX
    cZ
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem5
    3adantr2
    adantr
    @32
    cR
    @10
    cU
    cH
    cK
    cwun
    cX
    cY
    cZ
    funcringcsetcALTV2.r
    @22
    @28
    @27
    @29
    adantr
    #
    @10
    eqid
    @22
    cX
    cU
    wcel
    #
    @27
    @3
    wph
    @40
    @0
    @1
    wph
    @40
    wi
    @2
    wph
    @0
    @40
    wph
    cB
    cU
    cX
    wph
    cB
    cU
    crg
    cin
    cU
    wph
    cB
    cR
    cU
    cwun
    funcringcsetcALTV2.r
    funcringcsetcALTV2.b
    funcringcsetcALTV2.u
    ringcbas
    cU
    crg
    inss1
    syl6eqss
    #
    sseld
    com12
    3ad2ant1
    impcom
    adantr
    @22
    cY
    cU
    wcel
    #
    @27
    @3
    wph
    @42
    @1
    @0
    wph
    @42
    wi
    @2
    wph
    @1
    @42
    wph
    cB
    cU
    cY
    @41
    sseld
    com12
    3ad2ant2
    impcom
    adantr
    @22
    cZ
    cU
    wcel
    #
    @27
    @3
    wph
    @43
    @2
    @0
    wph
    @43
    wi
    @1
    wph
    @2
    @43
    wph
    cB
    cU
    cZ
    @41
    sseld
    com12
    3ad2ant3
    impcom
    adantr
    @24
    cX
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    cH
    wf
    #
    @22
    @26
    @44
    @45
    cX
    cY
    cH
    @44
    eqid
    @45
    eqid
    #
    rhmf
    ad2antrl
    #
    @26
    @45
    cZ
    cbs
    cfv
    #
    cK
    wf
    #
    @22
    @24
    @45
    @49
    cY
    cZ
    cK
    @47
    @49
    eqid
    rhmf
    ad2antll
    #
    ringcco
    fveq12d
    @32
    @20
    @14
    @15
    ccom
    @33
    @32
    cS
    @19
    cU
    @15
    @14
    cwun
    @16
    @17
    @18
    funcringcsetcALTV2.s
    @39
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
    @52
    @2
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cX
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem2
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
    @53
    @2
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cY
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem2
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
    @54
    @1
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cZ
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem2
    3ad2antr3
    adantr
    @32
    @16
    @17
    @15
    wf
    @16
    @17
    cH
    wf
    #
    @32
    @55
    @46
    @48
    @22
    @55
    @46
    wb
    @27
    @22
    @16
    @17
    @44
    @45
    cH
    wph
    @1
    @0
    @16
    @44
    wceq
    @2
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cX
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem1
    3ad2antr1
    wph
    @0
    @1
    @17
    @45
    wceq
    @2
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cY
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem1
    3ad2antr2
    #
    feq23d
    adantr
    mpbird
    @32
    @16
    @17
    @15
    cH
    @32
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
    @57
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
    cB
    cC
    cR
    cS
    cU
    cF
    cG
    cH
    cX
    cY
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem6
    syl3anc
    #
    feq1d
    mpbird
    @32
    @17
    @18
    @14
    wf
    @17
    @18
    cK
    wf
    #
    @32
    @60
    @50
    @51
    @22
    @60
    @50
    wb
    @27
    @22
    @17
    @18
    @45
    @49
    cK
    @56
    wph
    @0
    @2
    @18
    @49
    wceq
    @1
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    cZ
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem1
    3ad2antr3
    feq23d
    adantr
    mpbird
    @32
    @17
    @18
    @14
    cK
    @32
    wph
    @1
    @2
    wa
    #
    @26
    @14
    cK
    wceq
    @58
    @3
    @61
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
    cB
    cC
    cR
    cS
    cU
    cF
    cG
    cK
    cY
    cZ
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem6
    syl3anc
    #
    feq1d
    mpbird
    setcco
    @32
    @14
    cK
    @15
    cH
    @62
    @59
    coeq12d
    eqtrd
    3eqtr4d
    ex
    sylbid
    3impia
end
