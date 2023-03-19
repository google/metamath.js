include "crp.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "clog.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "c1.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "cchp.mm"
include "caddc.mm"
include "csu.mm"
include "co1.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "rpre.mm"
include "pntsval.mm"
include "syl.mm"
include "oveq1d.mm"
include "mpteq2ia.mm"
include "selberg.mm"
include "eqeltri.mm"

theorem selbergs
  let vx: setvar x
  let cS: class S
  let vi: setvar i
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cR: class R
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )

  disjoint a i
  disjoint a x
  disjoint i x
  disjoint S x
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a y
  disjoint A a
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S y
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- ( x e. RR+ |-> ( ( ( S ` x ) / x ) - ( 2 x. ( log ` x ) ) ) ) e. O(1)

  proof
    vx
    crp
    vx
    cv
    #
    cS
    cfv
    #
    @0
    cdiv
    co
    #
    c2
    @0
    clog
    cfv
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    vx
    crp
    c1
    @0
    cfl
    cfv
    cfz
    co
    vn
    cv
    #
    cvma
    cfv
    @5
    clog
    cfv
    @0
    @5
    cdiv
    co
    cchp
    cfv
    caddc
    co
    cmul
    co
    vn
    csu
    #
    @0
    cdiv
    co
    #
    @3
    cmin
    co
    #
    cmpt
    co1
    vx
    crp
    @4
    @8
    @0
    crp
    wcel
    #
    @2
    @7
    @3
    cmin
    @9
    @1
    @6
    @0
    cdiv
    @9
    @0
    cr
    wcel
    @1
    @6
    wceq
    @0
    rpre
    @0
    cS
    vi
    vn
    va
    pntsval.1
    pntsval
    syl
    oveq1d
    oveq1d
    mpteq2ia
    vx
    vn
    selberg
    eqeltri
end
