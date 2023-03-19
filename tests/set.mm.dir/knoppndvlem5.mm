include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "knoppcnlem3.mm"
include "fsumrecl.mm"

theorem knoppndvlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cN: class N
  assume knoppndvlem5.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem5.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem5.a: |- ( ph -> A e. RR )
  assume knoppndvlem5.c: |- ( ph -> C e. RR )
  assume knoppndvlem5.n: |- ( ph -> N e. NN )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint A x
  disjoint C n
  disjoint C y
  disjoint J i
  disjoint J n
  disjoint J y
  disjoint i n
  disjoint i y
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph y
  disjoint i x
  assert |- ( ph -> sum_ i e. ( 0 ... J ) ( ( F ` A ) ` i ) e. RR )

  proof
    wph
    cc0
    cJ
    cfz
    co
    #
    vi
    cv
    #
    cA
    cF
    cfv
    cfv
    vi
    wph
    cc0
    cJ
    fzfid
    wph
    @1
    @0
    wcel
    #
    wa
    vx
    vy
    cA
    cC
    cT
    vn
    cF
    @1
    cN
    knoppndvlem5.t
    knoppndvlem5.f
    wph
    cN
    cn
    wcel
    @2
    knoppndvlem5.n
    adantr
    wph
    cC
    cr
    wcel
    @2
    knoppndvlem5.c
    adantr
    wph
    cA
    cr
    wcel
    @2
    knoppndvlem5.a
    adantr
    @2
    @1
    cn0
    wcel
    wph
    @1
    cJ
    elfznn0
    adantl
    knoppcnlem3
    fsumrecl
end
