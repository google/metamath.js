include "cr.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "knoppcn.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnd.mm"

theorem knoppcld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cW: class W
  assume knoppcld.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcld.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcld.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppcld.a: |- ( ph -> A e. RR )
  assume knoppcld.n: |- ( ph -> N e. NN )
  assume knoppcld.1: |- ( ph -> C e. RR )
  assume knoppcld.2: |- ( ph -> ( abs ` C ) < 1 )

  disjoint C n
  disjoint C y
  disjoint n y
  disjoint F i
  disjoint F w
  disjoint i w
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint i n
  disjoint i y
  disjoint n w
  disjoint w y
  disjoint i x
  disjoint w x
  assert |- ( ph -> ( W ` A ) e. CC )

  proof
    wph
    cr
    cc
    cA
    cW
    wph
    cW
    cr
    cc
    ccncf
    co
    wcel
    cr
    cc
    cW
    wf
    wph
    vx
    vy
    vw
    cC
    cT
    vi
    vn
    cF
    cN
    cW
    knoppcld.t
    knoppcld.f
    knoppcld.w
    knoppcld.n
    knoppcld.1
    knoppcld.2
    knoppcn
    cr
    cc
    cW
    cncff
    syl
    knoppcld.a
    ffvelrnd
end
