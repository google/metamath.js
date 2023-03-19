include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "knoppf.mm"
include "cc.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "simprd.mm"
include "knoppcn.mm"
include "jca.mm"
include "cncffvrn.mm"
include "syl.mm"
include "mpbird.mm"

theorem knoppcn2
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
  assume knoppcn2.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcn2.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcn2.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppcn2.n: |- ( ph -> N e. NN )
  assume knoppcn2.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )

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
  assert |- ( ph -> W e. ( RR -cn-> RR ) )

  proof
    wph
    cW
    cr
    cr
    ccncf
    co
    wcel
    #
    cr
    cr
    cW
    wf
    #
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
    knoppcn2.t
    knoppcn2.f
    knoppcn2.w
    knoppcn2.c
    knoppcn2.n
    knoppf
    wph
    cr
    cc
    wss
    #
    cW
    cr
    cc
    ccncf
    co
    wcel
    #
    wa
    @0
    @1
    wb
    wph
    @2
    @3
    @2
    wph
    ax-resscn
    a1i
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
    knoppcn2.t
    knoppcn2.f
    knoppcn2.w
    knoppcn2.n
    wph
    cC
    cr
    wcel
    #
    cC
    cabs
    cfv
    c1
    clt
    wbr
    #
    wph
    cC
    knoppcn2.c
    knoppndvlem3
    #
    simpld
    wph
    @4
    @5
    @6
    simprd
    knoppcn
    jca
    cr
    cc
    cr
    cW
    cncffvrn
    syl
    mpbird
end
