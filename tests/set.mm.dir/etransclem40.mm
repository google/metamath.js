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
include "etransclem34.mm"

theorem etransclem40
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vn: setvar n
  let vm: setvar m
  let vy: setvar y
  assume etransclem40.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem40.a: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem40.p: |- ( ph -> P e. NN )
  assume etransclem40.m: |- ( ph -> M e. NN0 )
  assume etransclem40.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ k e. ( 1 ... M ) ( ( x - k ) ^ P ) ) )
  assume etransclem40.6: |- ( ph -> N e. NN0 )

  disjoint M k
  disjoint M x
  disjoint k x
  disjoint N k
  disjoint N x
  disjoint P k
  disjoint P x
  disjoint S k
  disjoint S x
  disjoint X k
  disjoint X x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint F c
  disjoint M c
  disjoint M d
  disjoint M j
  disjoint M n
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint k n
  disjoint n x
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint N c
  disjoint N n
  disjoint P c
  disjoint P j
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
  disjoint X j
  disjoint X n
  disjoint X y
  disjoint c ph
  disjoint n ph
  assert |- ( ph -> ( ( S Dn F ) ` N ) e. ( X -cn-> CC ) )

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
    vj
    cv
    #
    vd
    cv
    cfv
    vj
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
    vk
    vn
    cF
    vj
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
    cM
    cN
    cX
    vc
    etransclem40.s
    etransclem40.a
    etransclem40.p
    etransclem40.m
    etransclem40.f
    etransclem40.6
    vy
    vx
    cP
    vj
    vk
    cM
    cX
    etransclem5
    vj
    vk
    vn
    vm
    cM
    vd
    vc
    etransclem11
    etransclem34
end
