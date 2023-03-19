include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "crest.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "cr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "a1i.mm"
include "cnpf2.mm"
include "syl3anc.mm"

theorem ftc1lem3
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cX: class X
  let cE: class E
  let cH: class H
  let cY: class Y
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1.c: |- ( ph -> C e. ( A (,) B ) )
  assume ftc1.f: |- ( ph -> F e. ( ( K CnP L ) ` C ) )
  assume ftc1.j: |- J = ( L |`t RR )
  assume ftc1.k: |- K = ( L |`t D )
  assume ftc1.l: |- L = ( TopOpen ` CCfld )

  disjoint t x
  disjoint C t
  disjoint C x
  disjoint D t
  disjoint D x
  disjoint A t
  disjoint A x
  disjoint B t
  disjoint B x
  disjoint ph t
  disjoint ph x
  disjoint F t
  disjoint F x
  disjoint L x
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint d e
  disjoint G d
  disjoint e r
  disjoint e s
  disjoint e u
  disjoint e y
  disjoint e z
  disjoint G e
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G y
  disjoint G z
  disjoint A d
  disjoint e t
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint A e
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint Y t
  disjoint Y x
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L y
  disjoint L z
  disjoint R y
  assert |- ( ph -> F : D --> CC )

  proof
    wph
    cK
    cD
    ctopon
    cfv
    #
    wcel
    cL
    cc
    ctopon
    cfv
    wcel
    #
    cF
    cC
    cK
    cL
    ccnp
    co
    cfv
    wcel
    cD
    cc
    cF
    wf
    wph
    cK
    cL
    cD
    crest
    co
    #
    @0
    ftc1.k
    wph
    @1
    cD
    cc
    wss
    @2
    @0
    wcel
    cL
    ftc1.l
    cnfldtopon
    #
    wph
    cD
    cr
    cc
    ftc1.d
    ax-resscn
    syl6ss
    cD
    cL
    cc
    resttopon
    sylancr
    syl5eqel
    @1
    wph
    @3
    a1i
    ftc1.f
    cC
    cF
    cK
    cL
    cD
    cc
    cnpf2
    syl3anc
end
