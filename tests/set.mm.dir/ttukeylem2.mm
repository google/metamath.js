include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wi.mm"
include "simpr.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssrin.mm"
include "sstr2.mm"
include "3syl.mm"
include "wb.mm"
include "ttukeylem1.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "impancom.mm"
include "impr.mm"

theorem ttukeylem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let va: setvar a
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cG: class G
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )

  disjoint C x
  disjoint D x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
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
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F z
  assert |- ( ( ph /\ ( C e. A /\ D C_ C ) ) -> D e. A )

  proof
    wph
    cC
    cA
    wcel
    #
    cD
    cC
    wss
    #
    cD
    cA
    wcel
    #
    wph
    @1
    @0
    @2
    wph
    @1
    wa
    #
    cC
    cpw
    #
    cfn
    cin
    #
    cA
    wss
    #
    cD
    cpw
    #
    cfn
    cin
    #
    cA
    wss
    #
    @0
    @2
    @3
    @7
    @4
    wss
    #
    @8
    @5
    wss
    @6
    @9
    wi
    @3
    @1
    @10
    wph
    @1
    simpr
    cD
    cC
    sspwb
    sylib
    @7
    @4
    cfn
    ssrin
    @8
    @5
    cA
    sstr2
    3syl
    wph
    @0
    @6
    wb
    @1
    wph
    vx
    cA
    cB
    cC
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem1
    adantr
    wph
    @2
    @9
    wb
    @1
    wph
    vx
    cA
    cB
    cD
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem1
    adantr
    3imtr4d
    impancom
    impr
end
