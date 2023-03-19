include "c0.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "cima.mm"
include "cif.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "con0.mm"
include "0elon.mm"
include "ttukeylem3.mm"
include "mpan2.mm"
include "uni0.mm"
include "eqcomi.mm"
include "iftruei.mm"
include "eqid.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem ttukeylem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
  assume ttukeylem.4: |- G = recs ( ( z e. _V |-> if ( dom z = U. dom z , if ( dom z = (/) , B , U. ran z ) , ( ( z ` U. dom z ) u. if ( ( ( z ` U. dom z ) u. { ( F ` U. dom z ) } ) e. A , { ( F ` U. dom z ) } , (/) ) ) ) ) )

  disjoint x z
  disjoint G x
  disjoint G z
  disjoint ph z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint x y
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint a f
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint G a
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G y
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  disjoint B y
  assert |- ( ph -> ( G ` (/) ) = B )

  proof
    wph
    c0
    cG
    cfv
    #
    c0
    c0
    cuni
    #
    wceq
    #
    c0
    c0
    wceq
    #
    cB
    cG
    c0
    cima
    cuni
    #
    cif
    #
    @1
    cG
    cfv
    #
    @6
    @1
    cF
    cfv
    csn
    #
    cun
    cA
    wcel
    @7
    c0
    cif
    cun
    #
    cif
    #
    cB
    wph
    c0
    con0
    wcel
    @0
    @9
    wceq
    0elon
    wph
    vx
    vz
    cA
    cB
    c0
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem3
    mpan2
    @9
    @5
    cB
    @2
    @5
    @8
    @1
    c0
    uni0
    eqcomi
    iftruei
    @3
    cB
    @4
    c0
    eqid
    iftruei
    eqtri
    syl6eq
end
