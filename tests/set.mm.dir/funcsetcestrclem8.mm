include "wcel.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wf.mm"
include "cmap.mm"
include "cbs.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "cv.mm"
include "elmapi.mm"
include "wb.mm"
include "simpr.mm"
include "ancomd.mm"
include "elmapg.mm"
include "syl.mm"
include "biimpar.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "csn.mm"
include "funcsetcestrclem1.mm"
include "fveq2d.mm"
include "eqid.mm"
include "1strbas.mm"
include "eqcomd.mm"
include "adantl.mm"
include "eqtrd.mm"
include "adantrl.mm"
include "eqtr4d.mm"
include "adantrr.mm"
include "oveq12d.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"
include "fssd.mm"
include "funcsetcestrclem5.mm"
include "cwun.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "adantrd.mm"
include "imp.mm"
include "adantld.mm"
include "setchom.mm"
include "funcsetcestrclem2.mm"
include "estrchom.mm"
include "feq123d.mm"
include "mpbird.mm"

theorem funcsetcestrclem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
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
  disjoint C f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  assert |- ( ( ph /\ ( X e. C /\ Y e. C ) ) -> ( X G Y ) : ( X ( Hom ` S ) Y ) --> ( ( F ` X ) ( Hom ` E ) ( F ` Y ) ) )

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
    wa
    #
    wa
    #
    cX
    cY
    cS
    chom
    cfv
    #
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cE
    chom
    cfv
    #
    co
    #
    cX
    cY
    cG
    co
    #
    wf
    cY
    cX
    cmap
    co
    #
    @7
    cbs
    cfv
    #
    @6
    cbs
    cfv
    #
    cmap
    co
    #
    cid
    @11
    cres
    #
    wf
    @3
    @11
    @11
    @14
    @15
    @11
    @11
    @15
    wf1o
    @11
    @11
    @15
    wf
    @3
    @11
    f1oi
    @11
    @11
    @15
    f1of
    mp1i
    @3
    vf
    @11
    @14
    vf
    cv
    #
    @11
    wcel
    #
    cX
    cY
    @16
    wf
    #
    @3
    @16
    @14
    wcel
    #
    @16
    cY
    cX
    elmapi
    @3
    @18
    @19
    @3
    @18
    wa
    @16
    @11
    @14
    @3
    @17
    @18
    @3
    @1
    @0
    wa
    @17
    @18
    wb
    @3
    @0
    @1
    wph
    @2
    simpr
    ancomd
    cY
    cX
    @16
    cC
    cC
    elmapg
    syl
    biimpar
    @3
    @14
    @11
    wceq
    @18
    @3
    @12
    cY
    @13
    cX
    cmap
    wph
    @1
    @12
    cY
    wceq
    @0
    wph
    @1
    wa
    #
    @12
    cnx
    cbs
    cfv
    #
    cY
    cop
    csn
    #
    cbs
    cfv
    #
    cY
    @20
    @7
    @22
    cbs
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
    fveq2d
    @1
    @23
    cY
    wceq
    wph
    @1
    cY
    @23
    cY
    @22
    cC
    @22
    eqid
    1strbas
    eqcomd
    adantl
    eqtrd
    adantrl
    wph
    @0
    @13
    cX
    wceq
    @1
    wph
    @0
    wa
    #
    @13
    @21
    cX
    cop
    csn
    #
    cbs
    cfv
    #
    cX
    @24
    @6
    @25
    cbs
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
    fveq2d
    @0
    cX
    @26
    wceq
    wph
    cX
    @25
    cC
    @25
    eqid
    1strbas
    adantl
    eqtr4d
    adantrr
    oveq12d
    adantr
    eleqtrrd
    ex
    syl5
    ssrdv
    fssd
    @3
    @5
    @11
    @9
    @14
    @10
    @15
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cX
    cY
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem5
    @3
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
    @2
    funcsetcestrc.u
    adantr
    #
    @4
    eqid
    wph
    @2
    cX
    cU
    wcel
    #
    wph
    @0
    @28
    @1
    wph
    @0
    @28
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
    biimpd
    adantrd
    imp
    wph
    @2
    cY
    cU
    wcel
    #
    wph
    @1
    @30
    @0
    wph
    @1
    @30
    wph
    cC
    cU
    cY
    @29
    eleq2d
    biimpd
    adantld
    imp
    setchom
    @3
    @13
    @12
    cE
    cU
    @8
    cwun
    @6
    @7
    funcsetcestrc.e
    @27
    @8
    eqid
    wph
    @0
    @6
    cU
    wcel
    @1
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
    adantrr
    wph
    @1
    @7
    cU
    wcel
    @0
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
    adantrl
    @13
    eqid
    @12
    eqid
    estrchom
    feq123d
    mpbird
end
