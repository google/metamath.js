include "cvv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wtru.mm"
include "w3a.mm"
include "tru.mm"
include "cv.mm"
include "wa.mm"
include "a1i.mm"
include "caovassg.mm"
include "mpan.mm"
include "mp3an.mm"

theorem caovass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cD: class D
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cS: class S
  let cT: class T
  assume caovass.1: |- A e. _V
  assume caovass.2: |- B e. _V
  assume caovass.3: |- C e. _V
  assume caovass.4: |- ( ( x F y ) F z ) = ( x F ( y F z ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A F B ) F C ) = ( A F ( B F C ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    cA
    cB
    cF
    co
    cC
    cF
    co
    cA
    cB
    cC
    cF
    co
    cF
    co
    wceq
    #
    caovass.1
    caovass.2
    caovass.3
    wtru
    @0
    @1
    @2
    w3a
    @3
    tru
    wtru
    vx
    vy
    vz
    cA
    cB
    cC
    cvv
    cF
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    vz
    cv
    #
    cF
    co
    @4
    @5
    @6
    cF
    co
    cF
    co
    wceq
    wtru
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @6
    cvv
    wcel
    w3a
    wa
    caovass.4
    a1i
    caovassg
    mpan
    mp3an
end
