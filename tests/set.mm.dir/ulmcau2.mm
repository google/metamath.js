include "culm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "ulmcau.mm"
include "ulmcaulem.mm"
include "bitrd.mm"

theorem ulmcau2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vg: setvar g
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume ulmcau.z: |- Z = ( ZZ>= ` M )
  assume ulmcau.m: |- ( ph -> M e. ZZ )
  assume ulmcau.s: |- ( ph -> S e. V )
  assume ulmcau.f: |- ( ph -> F : Z --> ( CC ^m S ) )

  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S x
  disjoint S z
  disjoint Z j
  disjoint Z k
  disjoint Z m
  disjoint Z x
  disjoint Z z
  disjoint M j
  disjoint M k
  disjoint M z
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint m v
  disjoint m w
  disjoint m y
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint p q
  disjoint p r
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q r
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint g ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint S g
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint Z g
  disjoint Z n
  disjoint Z p
  disjoint Z q
  disjoint Z r
  disjoint Z v
  disjoint Z w
  disjoint Z y
  disjoint M p
  disjoint M q
  disjoint M r
  disjoint M w
  assert |- ( ph -> ( F e. dom ( ~~>u ` S ) <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) A. m e. ( ZZ>= ` k ) A. z e. S ( abs ` ( ( ( F ` k ) ` z ) - ( ( F ` m ) ` z ) ) ) < x ) )

  proof
    wph
    cF
    cS
    culm
    cfv
    cdm
    wcel
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    cfv
    #
    @0
    vj
    cv
    #
    cF
    cfv
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    #
    clt
    wbr
    vz
    cS
    wral
    vk
    @3
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    vx
    crp
    wral
    @2
    @0
    vm
    cv
    cF
    cfv
    cfv
    cmin
    co
    cabs
    cfv
    @4
    clt
    wbr
    vz
    cS
    wral
    vm
    @1
    cuz
    cfv
    wral
    vk
    @5
    wral
    vj
    cZ
    wrex
    vx
    crp
    wral
    wph
    vx
    vz
    cS
    vj
    vk
    cF
    cM
    cV
    cZ
    ulmcau.z
    ulmcau.m
    ulmcau.s
    ulmcau.f
    ulmcau
    wph
    vx
    vz
    cS
    vj
    vk
    vm
    cF
    cM
    cV
    cZ
    ulmcau.z
    ulmcau.m
    ulmcau.s
    ulmcau.f
    ulmcaulem
    bitrd
end
