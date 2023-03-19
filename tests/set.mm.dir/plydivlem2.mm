include "cv.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmin.mm"
include "adantr.mm"
include "simpr.mm"
include "caddc.mm"
include "adantlr.mm"
include "plymul.mm"
include "c1.mm"
include "cneg.mm"
include "plysub.mm"
include "syl5eqel.mm"

theorem plydivlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vf: setvar f
  let vp: setvar p
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let cT: class T
  let vg: setvar g
  let vw: setvar w
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )
  assume plydiv.f: |- ( ph -> F e. ( Poly ` S ) )
  assume plydiv.g: |- ( ph -> G e. ( Poly ` S ) )
  assume plydiv.z: |- ( ph -> G =/= 0p )
  assume plydiv.r: |- R = ( F oF - ( G oF x. q ) )

  disjoint x y
  disjoint q x
  disjoint q y
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint G q
  disjoint G x
  disjoint G y
  disjoint R x
  disjoint R y
  disjoint S q
  disjoint S x
  disjoint S y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q z
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint G p
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R p
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S p
  disjoint S z
  assert |- ( ( ph /\ q e. ( Poly ` S ) ) -> R e. ( Poly ` S ) )

  proof
    wph
    vq
    cv
    #
    cS
    cply
    cfv
    #
    wcel
    #
    wa
    #
    cR
    cF
    cG
    @0
    cmul
    cof
    co
    #
    cmin
    cof
    co
    @1
    plydiv.r
    @3
    vx
    vy
    cS
    cF
    @4
    wph
    cF
    @1
    wcel
    @2
    plydiv.f
    adantr
    @3
    vx
    vy
    cS
    cG
    @0
    wph
    cG
    @1
    wcel
    @2
    plydiv.g
    adantr
    wph
    @2
    simpr
    wph
    vx
    cv
    #
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @5
    @6
    caddc
    co
    cS
    wcel
    @2
    plydiv.pl
    adantlr
    #
    wph
    @7
    @5
    @6
    cmul
    co
    cS
    wcel
    @2
    plydiv.tm
    adantlr
    #
    plymul
    @8
    @9
    wph
    c1
    cneg
    cS
    wcel
    @2
    plydiv.m1
    adantr
    plysub
    syl5eqel
end
