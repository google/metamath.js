include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "chom.mm"
include "eqid.mm"
include "cwun.mm"
include "wcel.mm"
include "ccat.mm"
include "ringccat.mm"
include "syl.mm"
include "setccat.mm"
include "funcringcsetcALTV2lem3.mm"
include "funcringcsetcALTV2lem4.mm"
include "cv.mm"
include "funcringcsetcALTV2lem8.mm"
include "funcringcsetcALTV2lem7.mm"
include "funcringcsetcALTV2lem9.mm"
include "isfuncd.mm"

theorem funcringcsetcALTV2
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
  assume funcringcsetcALTV2.r: |- R = ( RingCat ` U )
  assume funcringcsetcALTV2.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV2.b: |- B = ( Base ` R )
  assume funcringcsetcALTV2.c: |- C = ( Base ` S )
  assume funcringcsetcALTV2.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV2.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV2.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

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
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
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
    funcringcsetcALTV2.u
    cR
    cU
    cwun
    funcringcsetcALTV2.r
    ringccat
    syl
    wph
    @6
    cS
    ccat
    wcel
    funcringcsetcALTV2.u
    cS
    cU
    cwun
    funcringcsetcALTV2.s
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
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2lem3
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
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem4
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
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem8
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
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem7
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
    funcringcsetcALTV2.r
    funcringcsetcALTV2.s
    funcringcsetcALTV2.b
    funcringcsetcALTV2.c
    funcringcsetcALTV2.u
    funcringcsetcALTV2.f
    funcringcsetcALTV2.g
    funcringcsetcALTV2lem9
    isfuncd
end
