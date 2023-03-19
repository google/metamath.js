include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "cv.mm"
include "a1i.mm"
include "caovcomg.mm"
include "mp2an.mm"

theorem caovcom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z
  let cC: class C
  let cD: class D
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cS: class S
  let cT: class T
  assume caovcom.1: |- A e. _V
  assume caovcom.2: |- B e. _V
  assume caovcom.3: |- ( x F y ) = ( y F x )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint F z
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
  assert |- ( A F B ) = ( B F A )

  proof
    cA
    cvv
    wcel
    #
    @0
    cB
    cvv
    wcel
    #
    wa
    cA
    cB
    cF
    co
    cB
    cA
    cF
    co
    wceq
    caovcom.1
    @0
    @1
    caovcom.1
    caovcom.2
    pm3.2i
    @0
    vx
    vy
    cA
    cB
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
    @3
    @2
    cF
    co
    wceq
    @0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    wa
    wa
    caovcom.3
    a1i
    caovcomg
    mp2an
end
