include "cr.mm"
include "caddc.mm"
include "cof.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "nn0uz.mm"
include "0zd.mm"
include "knoppcnlem11.mm"
include "knoppcnlem9.mm"
include "ulmcn.mm"

theorem knoppcn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cW: class W
  let vm: setvar m
  let vz: setvar z
  assume knoppcn.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcn.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcn.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppcn.n: |- ( ph -> N e. NN )
  assume knoppcn.1: |- ( ph -> C e. RR )
  assume knoppcn.2: |- ( ph -> ( abs ` C ) < 1 )

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
  disjoint C m
  disjoint m n
  disjoint m y
  disjoint F m
  disjoint F z
  disjoint i m
  disjoint i z
  disjoint m w
  disjoint m z
  disjoint w z
  disjoint m ph
  disjoint ph z
  disjoint n z
  disjoint y z
  disjoint m x
  disjoint x z
  assert |- ( ph -> W e. ( RR -cn-> CC ) )

  proof
    wph
    cr
    caddc
    cof
    vm
    cn0
    vz
    cr
    vm
    cv
    vz
    cv
    cF
    cfv
    cfv
    cmpt
    cmpt
    cc0
    cseq
    cW
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    vx
    vy
    vz
    cC
    cT
    vm
    vn
    cF
    cN
    knoppcn.t
    knoppcn.f
    knoppcn.n
    knoppcn.1
    knoppcnlem11
    wph
    vx
    vy
    vz
    vw
    cC
    cT
    vi
    vm
    vn
    cF
    cN
    cW
    knoppcn.t
    knoppcn.f
    knoppcn.w
    knoppcn.n
    knoppcn.1
    knoppcn.2
    knoppcnlem9
    ulmcn
end
