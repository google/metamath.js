include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cmin.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "etransclem11.mm"
include "etransclem36.mm"

theorem etransclem42
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m
  let vy: setvar y
  assume etransclem42.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem42.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem42.p: |- ( ph -> P e. NN )
  assume etransclem42.m: |- ( ph -> M e. NN0 )
  assume etransclem42.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem42.n: |- ( ph -> N e. NN0 )
  assume etransclem42.jx: |- ( ph -> J e. X )
  assume etransclem42.jz: |- ( ph -> J e. ZZ )

  disjoint J j
  disjoint J x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N j
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S j
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint J c
  disjoint c j
  disjoint c x
  disjoint M c
  disjoint M d
  disjoint M k
  disjoint M n
  disjoint c d
  disjoint c k
  disjoint c n
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d x
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint j m
  disjoint m n
  disjoint m x
  disjoint N c
  disjoint N n
  disjoint P c
  disjoint P k
  disjoint P n
  disjoint P y
  disjoint c y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint S c
  disjoint S n
  disjoint X c
  disjoint X k
  disjoint X n
  disjoint X y
  disjoint c ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ( ( S Dn F ) ` N ) ` J ) e. ZZ )

  proof
    wph
    vx
    vm
    cn0
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @2
    cfz
    co
    @0
    cmap
    co
    crab
    cmpt
    cP
    cS
    vj
    vn
    cF
    vk
    @0
    vy
    cX
    vy
    cv
    @1
    cmin
    co
    @1
    cc0
    wceq
    cP
    c1
    cmin
    co
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    cJ
    cM
    cN
    cX
    vc
    etransclem42.s
    etransclem42.x
    etransclem42.p
    etransclem42.m
    etransclem42.f
    etransclem42.n
    vy
    vx
    cP
    vk
    vj
    cM
    cX
    etransclem5
    etransclem42.jx
    etransclem42.jz
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    etransclem36
end
