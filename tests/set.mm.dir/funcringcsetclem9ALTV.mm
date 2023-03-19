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
include "ringchomALTV.mm"
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
include "funcringcsetclem5ALTV.mm"
include "3adantr2.mm"
include "simprl.mm"
include "simprr.mm"
include "ringccoALTV.mm"
include "fveq12d.mm"
include "funcringcsetclem2ALTV.mm"
include "3ad2antr1.mm"
include "3ad2antr2.mm"
include "3ad2antr3.mm"
include "wf.mm"
include "cbs.mm"
include "rhmf.mm"
include "ad2antrl.mm"
include "wb.mm"
include "funcringcsetclem1ALTV.mm"
include "feq23d.mm"
include "mpbird.mm"
include "simpll.mm"
include "3simpa.mm"
include "ad2antlr.mm"
include "funcringcsetclem6ALTV.mm"
include "syl3anc.mm"
include "feq1d.mm"
include "ad2antll.mm"
include "3simpc.mm"
include "setcco.mm"
include "coeq12d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"

theorem funcringcsetclem9ALTV
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
  assume funcringcsetcALTV.r: |- R = ( RingCatALTV ` U )
  assume funcringcsetcALTV.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV.b: |- B = ( Base ` R )
  assume funcringcsetcALTV.c: |- C = ( Base ` S )
  assume funcringcsetcALTV.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

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
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    wph
    cU
    cwun
    wcel
    #
    @3
    funcringcsetcALTV.u
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
    #
    wph
    @0
    @1
    @2
    simpr2
    #
    ringchomALTV
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
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    @29
    @30
    @32
    wph
    @0
    @1
    @2
    simpr3
    #
    ringchomALTV
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
    @35
    @13
    @20
    @34
    @35
    @36
    wcel
    #
    @38
    @35
    wceq
    @27
    @39
    @22
    @26
    @24
    @39
    cX
    cY
    cZ
    cK
    cH
    rhmco
    ancoms
    adantl
    @36
    @35
    fvresi
    syl
    @34
    @11
    @35
    @12
    @37
    @22
    @12
    @37
    wceq
    #
    @27
    wph
    @0
    @2
    @40
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem5ALTV
    3adantr2
    adantr
    @34
    cB
    cR
    @10
    cU
    cH
    cK
    cwun
    cX
    cY
    cZ
    funcringcsetcALTV.r
    funcringcsetcALTV.b
    @22
    @28
    @27
    @29
    adantr
    #
    @10
    eqid
    @22
    @0
    @27
    @31
    adantr
    @22
    @1
    @27
    @32
    adantr
    @22
    @2
    @27
    @33
    adantr
    @22
    @24
    @26
    simprl
    #
    @22
    @24
    @26
    simprr
    #
    ringccoALTV
    fveq12d
    @34
    @20
    @14
    @15
    ccom
    @35
    @34
    cS
    @19
    cU
    @15
    @14
    cwun
    @16
    @17
    @18
    funcringcsetcALTV.s
    @41
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
    @44
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem2ALTV
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
    @45
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem2ALTV
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
    @46
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem2ALTV
    3ad2antr3
    adantr
    @34
    @16
    @17
    @15
    wf
    @16
    @17
    cH
    wf
    #
    @34
    @47
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
    @24
    @50
    @22
    @26
    @48
    @49
    cX
    cY
    cH
    @48
    eqid
    @49
    eqid
    #
    rhmf
    ad2antrl
    @22
    @47
    @50
    wb
    @27
    @22
    @16
    @17
    @48
    @49
    cH
    wph
    @1
    @0
    @16
    @48
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem1ALTV
    3ad2antr1
    wph
    @0
    @1
    @17
    @49
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem1ALTV
    3ad2antr2
    #
    feq23d
    adantr
    mpbird
    @34
    @16
    @17
    @15
    cH
    @34
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
    @53
    wph
    @27
    @0
    @1
    @2
    3simpa
    ad2antlr
    @42
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem6ALTV
    syl3anc
    #
    feq1d
    mpbird
    @34
    @17
    @18
    @14
    wf
    @17
    @18
    cK
    wf
    #
    @34
    @56
    @49
    cZ
    cbs
    cfv
    #
    cK
    wf
    #
    @26
    @58
    @22
    @24
    @49
    @57
    cY
    cZ
    cK
    @51
    @57
    eqid
    rhmf
    ad2antll
    @22
    @56
    @58
    wb
    @27
    @22
    @17
    @18
    @49
    @57
    cK
    @52
    wph
    @0
    @2
    @18
    @57
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem1ALTV
    3ad2antr3
    feq23d
    adantr
    mpbird
    @34
    @17
    @18
    @14
    cK
    @34
    wph
    @1
    @2
    wa
    #
    @26
    @14
    cK
    wceq
    @54
    @3
    @59
    wph
    @27
    @0
    @1
    @2
    3simpc
    ad2antlr
    @43
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem6ALTV
    syl3anc
    #
    feq1d
    mpbird
    setcco
    @34
    @14
    cK
    @15
    cH
    @60
    @55
    coeq12d
    eqtrd
    3eqtr4d
    ex
    sylbid
    3impia
end
