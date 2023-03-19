include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "chom.mm"
include "eqid.mm"
include "cwun.mm"
include "wcel.mm"
include "ccat.mm"
include "ringccatALTV.mm"
include "syl.mm"
include "setccat.mm"
include "funcringcsetclem3ALTV.mm"
include "funcringcsetclem4ALTV.mm"
include "cv.mm"
include "funcringcsetclem8ALTV.mm"
include "funcringcsetclem7ALTV.mm"
include "funcringcsetclem9ALTV.mm"
include "isfuncd.mm"

theorem funcringcsetcALTV
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
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vk: setvar k
  assume funcringcsetcALTV.r: |- R = ( RingCatALTV ` U )
  assume funcringcsetcALTV.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV.b: |- B = ( Base ` R )
  assume funcringcsetcALTV.c: |- C = ( Base ` S )
  assume funcringcsetcALTV.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  disjoint Z x
  disjoint Z y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B h
  disjoint B k
  disjoint a h
  disjoint a k
  disjoint b h
  disjoint b k
  disjoint c h
  disjoint c k
  disjoint h k
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F h
  disjoint F k
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G h
  disjoint G k
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R h
  disjoint R k
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S h
  disjoint S k
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint h ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> F ( R Func S ) G )

  proof
    wph
    va
    vb
    vc
    cB
    cC
    cR
    cR
    cco
    cfv
    #
    cR
    ccid
    cfv
    #
    vh
    vk
    cS
    cF
    cG
    cR
    chom
    cfv
    #
    cS
    ccid
    cfv
    #
    cS
    chom
    cfv
    #
    cS
    cco
    cfv
    #
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    @2
    eqid
    @4
    eqid
    @1
    eqid
    @3
    eqid
    @0
    eqid
    @5
    eqid
    wph
    cU
    cwun
    wcel
    #
    cR
    ccat
    wcel
    funcringcsetcALTV.u
    cR
    cU
    cwun
    funcringcsetcALTV.r
    ringccatALTV
    syl
    wph
    @6
    cS
    ccat
    wcel
    funcringcsetcALTV.u
    cS
    cU
    cwun
    funcringcsetcALTV.s
    setccat
    syl
    wph
    vx
    cB
    cC
    cR
    cS
    cU
    cF
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetclem3ALTV
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
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem4ALTV
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
    va
    cv
    #
    vb
    cv
    #
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem8ALTV
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
    @7
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem7ALTV
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
    vh
    cv
    vk
    cv
    @7
    @8
    vc
    cv
    funcringcsetcALTV.r
    funcringcsetcALTV.s
    funcringcsetcALTV.b
    funcringcsetcALTV.c
    funcringcsetcALTV.u
    funcringcsetcALTV.f
    funcringcsetcALTV.g
    funcringcsetclem9ALTV
    isfuncd
end
