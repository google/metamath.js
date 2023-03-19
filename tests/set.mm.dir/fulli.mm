include "co.mm"
include "cfv.mm"
include "wfo.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "fullfo.mm"
include "foelrn.mm"
include "syl2anc.mm"

theorem fulli
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume isfull.b: |- B = ( Base ` C )
  assume isfull.j: |- J = ( Hom ` D )
  assume isfull.h: |- H = ( Hom ` C )
  assume fullfo.f: |- ( ph -> F ( C Full D ) G )
  assume fullfo.x: |- ( ph -> X e. B )
  assume fullfo.y: |- ( ph -> Y e. B )
  assume fulli.r: |- ( ph -> R e. ( ( F ` X ) J ( F ` Y ) ) )

  disjoint B f
  disjoint C f
  disjoint D f
  disjoint H f
  disjoint J f
  disjoint R f
  disjoint X f
  disjoint Y f
  disjoint F f
  disjoint G f
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint d y
  disjoint B d
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C c
  disjoint C d
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint D c
  disjoint D d
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint H x
  disjoint H y
  disjoint J c
  disjoint J d
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G x
  disjoint G y
  assert |- ( ph -> E. f e. ( X H Y ) R = ( ( X G Y ) ` f ) )

  proof
    wph
    cX
    cY
    cH
    co
    #
    cX
    cF
    cfv
    cY
    cF
    cfv
    cJ
    co
    #
    cX
    cY
    cG
    co
    #
    wfo
    cR
    @1
    wcel
    cR
    vf
    cv
    @2
    cfv
    wceq
    vf
    @0
    wrex
    wph
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    cX
    cY
    isfull.b
    isfull.j
    isfull.h
    fullfo.f
    fullfo.x
    fullfo.y
    fullfo
    fulli.r
    vf
    @0
    @1
    cR
    @2
    foelrn
    syl2anc
end
