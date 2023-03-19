include "cr.mm"
include "wf.mm"
include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "wi.mm"
include "dvfsumrlimf.mm"
include "dvfsumrlim.mm"
include "wa.mm"
include "csb.mm"
include "cz.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "adantlr.mm"
include "cmpt.mm"
include "cdv.mm"
include "wceq.mm"
include "3adant1r.mm"
include "cc0.mm"
include "simprr.mm"
include "simprl.mm"
include "dvfsumrlim2.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "syl.mm"
include "breqtrd.mm"
include "exp42.mm"
include "com24.mm"
include "3impd.mm"
include "3jca.mm"

theorem dvfsumrlim3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cL: class L
  let cM: class M
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let vm: setvar m
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cY: class Y
  let cU: class U
  assume dvfsum.s: |- S = ( T (,) +oo )
  assume dvfsum.z: |- Z = ( ZZ>= ` M )
  assume dvfsum.m: |- ( ph -> M e. ZZ )
  assume dvfsum.d: |- ( ph -> D e. RR )
  assume dvfsum.md: |- ( ph -> M <_ ( D + 1 ) )
  assume dvfsum.t: |- ( ph -> T e. RR )
  assume dvfsum.a: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume dvfsum.b1: |- ( ( ph /\ x e. S ) -> B e. V )
  assume dvfsum.b2: |- ( ( ph /\ x e. Z ) -> B e. RR )
  assume dvfsum.b3: |- ( ph -> ( RR _D ( x e. S |-> A ) ) = ( x e. S |-> B ) )
  assume dvfsum.c: |- ( x = k -> B = C )
  assume dvfsumrlim.l: |- ( ( ph /\ ( x e. S /\ k e. S ) /\ ( D <_ x /\ x <_ k ) ) -> C <_ B )
  assume dvfsumrlim.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )
  assume dvfsumrlim.k: |- ( ph -> ( x e. S |-> B ) ~~>r 0 )
  assume dvfsumrlim3.1: |- ( x = X -> B = E )

  disjoint B k
  disjoint C x
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint E x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint M k
  disjoint M x
  disjoint T x
  disjoint Z x
  disjoint X k
  disjoint X x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint c e
  disjoint c k
  disjoint c m
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint e k
  disjoint e m
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint x z
  disjoint C z
  disjoint c x
  disjoint D c
  disjoint x y
  disjoint D y
  disjoint E y
  disjoint G c
  disjoint G e
  disjoint G y
  disjoint G z
  disjoint H m
  disjoint H y
  disjoint H z
  disjoint c ph
  disjoint e x
  disjoint e ph
  disjoint m x
  disjoint m ph
  disjoint ph y
  disjoint S c
  disjoint S e
  disjoint S m
  disjoint S y
  disjoint S z
  disjoint L y
  disjoint M z
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint T c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w z
  disjoint T w
  disjoint T z
  disjoint Y k
  disjoint Y m
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint U k
  disjoint U x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint X m
  disjoint u y
  disjoint X u
  disjoint v y
  disjoint X v
  disjoint w y
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( G : S --> RR /\ G e. dom ~~>r /\ ( ( G ~~>r L /\ X e. S /\ D <_ X ) -> ( abs ` ( ( G ` X ) - L ) ) <_ E ) ) )

  proof
    wph
    cS
    cr
    cG
    wf
    cG
    crli
    cdm
    wcel
    cG
    cL
    crli
    wbr
    #
    cX
    cS
    wcel
    #
    cD
    cX
    cle
    wbr
    #
    w3a
    cX
    cG
    cfv
    cL
    cmin
    co
    cabs
    cfv
    #
    cE
    cle
    wbr
    #
    wi
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.g
    dvfsumrlimf
    wph
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cM
    cV
    cZ
    dvfsum.s
    dvfsum.z
    dvfsum.m
    dvfsum.d
    dvfsum.md
    dvfsum.t
    dvfsum.a
    dvfsum.b1
    dvfsum.b2
    dvfsum.b3
    dvfsum.c
    dvfsumrlim.l
    dvfsumrlim.g
    dvfsumrlim.k
    dvfsumrlim
    wph
    @0
    @1
    @2
    @4
    wph
    @2
    @1
    @0
    @4
    wph
    @2
    @1
    @0
    @4
    wph
    @2
    @1
    wa
    #
    wa
    #
    @0
    wa
    #
    @3
    vx
    cX
    cB
    csb
    #
    cE
    cle
    @6
    vx
    cA
    cB
    cC
    cD
    cS
    cT
    vk
    cG
    cL
    cM
    cV
    cX
    cZ
    dvfsum.s
    dvfsum.z
    wph
    cM
    cz
    wcel
    @5
    dvfsum.m
    adantr
    wph
    cD
    cr
    wcel
    @5
    dvfsum.d
    adantr
    wph
    cM
    cD
    c1
    caddc
    co
    cle
    wbr
    @5
    dvfsum.md
    adantr
    wph
    cT
    cr
    wcel
    @5
    dvfsum.t
    adantr
    wph
    vx
    cv
    #
    cS
    wcel
    #
    cA
    cr
    wcel
    @5
    dvfsum.a
    adantlr
    wph
    @10
    cB
    cV
    wcel
    @5
    dvfsum.b1
    adantlr
    wph
    @9
    cZ
    wcel
    cB
    cr
    wcel
    @5
    dvfsum.b2
    adantlr
    wph
    cr
    vx
    cS
    cA
    cmpt
    cdv
    co
    vx
    cS
    cB
    cmpt
    #
    wceq
    @5
    dvfsum.b3
    adantr
    dvfsum.c
    wph
    @10
    vk
    cv
    #
    cS
    wcel
    wa
    cD
    @9
    cle
    wbr
    @9
    @12
    cle
    wbr
    wa
    cC
    cB
    cle
    wbr
    @5
    dvfsumrlim.l
    3adant1r
    dvfsumrlim.g
    wph
    @11
    cc0
    crli
    wbr
    @5
    dvfsumrlim.k
    adantr
    wph
    @2
    @1
    simprr
    #
    wph
    @2
    @1
    simprl
    dvfsumrlim2
    @7
    @1
    @8
    cE
    wceq
    @6
    @1
    @0
    @13
    adantr
    vx
    cX
    cB
    cE
    cS
    @1
    vx
    cE
    nfcvd
    dvfsumrlim3.1
    csbiegf
    syl
    breqtrd
    exp42
    com24
    3impd
    3jca
end
