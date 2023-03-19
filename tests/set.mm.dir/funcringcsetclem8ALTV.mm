include "wcel.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wf.mm"
include "crh.mm"
include "cmap.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "cv.mm"
include "cbs.mm"
include "eqid.mm"
include "rhmf.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "bicomd.mm"
include "biimpa.mm"
include "wceq.mm"
include "simpr.mm"
include "funcringcsetclem1ALTV.mm"
include "sylan2.mm"
include "simpl.mm"
include "oveq12d.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"
include "fssd.mm"
include "funcringcsetclem5ALTV.mm"
include "cwun.mm"
include "adantl.mm"
include "ringchomALTV.mm"
include "funcringcsetclem2ALTV.mm"
include "setchom.mm"
include "feq123d.mm"
include "mpbird.mm"

theorem funcringcsetclem8ALTV
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
  let cX: class X
  let cY: class Y
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
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  disjoint k x
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X G Y ) : ( X ( Hom ` R ) Y ) --> ( ( F ` X ) ( Hom ` S ) ( F ` Y ) ) )

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
    wa
    #
    wa
    #
    cX
    cY
    cR
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
    cS
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
    cX
    cY
    crh
    co
    #
    @7
    @6
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
    @12
    @13
    @11
    @11
    @13
    wf1o
    @11
    @11
    @13
    wf
    @3
    @11
    f1oi
    @11
    @11
    @13
    f1of
    mp1i
    @3
    vf
    @11
    @12
    vf
    cv
    #
    @11
    wcel
    cX
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    @14
    wf
    #
    @3
    @14
    @12
    wcel
    #
    @15
    @16
    cX
    cY
    @14
    @15
    eqid
    @16
    eqid
    rhmf
    @3
    @17
    @18
    @3
    @17
    wa
    @14
    @16
    @15
    cmap
    co
    #
    @12
    @3
    @17
    @14
    @19
    wcel
    #
    @16
    cvv
    wcel
    #
    @15
    cvv
    wcel
    #
    wa
    #
    @17
    @20
    wb
    @3
    @21
    @22
    cY
    cbs
    fvex
    cX
    cbs
    fvex
    pm3.2i
    @23
    @20
    @17
    @16
    @15
    @14
    cvv
    cvv
    elmapg
    bicomd
    mp1i
    biimpa
    @3
    @12
    @19
    wceq
    @17
    @3
    @7
    @16
    @6
    @15
    cmap
    @2
    wph
    @1
    @7
    @16
    wceq
    @0
    @1
    simpr
    #
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
    sylan2
    @2
    wph
    @0
    @6
    @15
    wceq
    @0
    @1
    simpl
    #
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
    sylan2
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
    @12
    @10
    @13
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
    cY
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem5ALTV
    @3
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
    @2
    funcringcsetcALTV.u
    adantr
    #
    @4
    eqid
    @2
    @0
    wph
    @25
    adantl
    @2
    @1
    wph
    @24
    adantl
    ringchomALTV
    @3
    cS
    cU
    @8
    cwun
    @6
    @7
    funcringcsetcALTV.s
    @26
    @8
    eqid
    @2
    wph
    @0
    @6
    cU
    wcel
    @25
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
    sylan2
    @2
    wph
    @1
    @7
    cU
    wcel
    @24
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
    sylan2
    setchom
    feq123d
    mpbird
end
