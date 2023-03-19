include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cr.mm"
include "wrex.mm"
include "cn0.mm"
include "knoppndvlem20.mm"
include "knoppndvlem18.mm"
include "wcel.mm"
include "eqid.mm"
include "cioo.mm"
include "adantr.mm"
include "crp.mm"
include "simprl.mm"
include "cn.mm"
include "simprrl.mm"
include "simprrr.mm"
include "knoppndvlem21.mm"
include "rexlimddv.mm"

theorem knoppndvlem22
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  assume knoppndvlem22.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem22.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem22.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem22.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem22.d: |- ( ph -> D e. RR+ )
  assume knoppndvlem22.e: |- ( ph -> E e. RR+ )
  assume knoppndvlem22.h: |- ( ph -> H e. RR )
  assume knoppndvlem22.n: |- ( ph -> N e. NN )
  assume knoppndvlem22.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

  disjoint C i
  disjoint C n
  disjoint C w
  disjoint C y
  disjoint i n
  disjoint i w
  disjoint i y
  disjoint n w
  disjoint n y
  disjoint w y
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D y
  disjoint E a
  disjoint E b
  disjoint E i
  disjoint E n
  disjoint E w
  disjoint E y
  disjoint F i
  disjoint F w
  disjoint H a
  disjoint H b
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N n
  disjoint N w
  disjoint N y
  disjoint N x
  disjoint i x
  disjoint w x
  disjoint T n
  disjoint T y
  disjoint W a
  disjoint W b
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint C j
  disjoint i j
  disjoint j n
  disjoint j w
  disjoint j y
  disjoint D j
  disjoint a j
  disjoint b j
  disjoint E j
  disjoint H j
  disjoint N j
  disjoint j x
  disjoint W j
  disjoint j ph
  assert |- ( ph -> E. a e. RR E. b e. RR ( ( a <_ H /\ H <_ b ) /\ ( ( b - a ) < D /\ a =/= b ) /\ E <_ ( ( abs ` ( ( W ` b ) - ( W ` a ) ) ) / ( b - a ) ) ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    vj
    cv
    #
    cneg
    cexp
    co
    c2
    cdiv
    co
    cD
    clt
    wbr
    #
    cE
    @0
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    @1
    cexp
    co
    c1
    c1
    @4
    c1
    cmin
    co
    cdiv
    co
    cmin
    co
    #
    cmul
    co
    cle
    wbr
    #
    wa
    #
    va
    cv
    #
    cH
    cle
    wbr
    cH
    vb
    cv
    #
    cle
    wbr
    wa
    @9
    @8
    cmin
    co
    #
    cD
    clt
    wbr
    @8
    @9
    wne
    wa
    cE
    @9
    cW
    cfv
    @8
    cW
    cfv
    cmin
    co
    cabs
    cfv
    @10
    cdiv
    co
    cle
    wbr
    w3a
    vb
    cr
    wrex
    va
    cr
    wrex
    vj
    cn0
    wph
    cC
    cD
    vj
    cE
    @5
    cN
    knoppndvlem22.c
    knoppndvlem22.n
    knoppndvlem22.d
    knoppndvlem22.e
    wph
    cC
    cN
    knoppndvlem22.c
    knoppndvlem22.n
    knoppndvlem22.1
    knoppndvlem20
    knoppndvlem22.1
    knoppndvlem18
    wph
    @1
    cn0
    wcel
    #
    @7
    wa
    #
    wa
    vx
    vy
    vw
    cC
    cD
    cT
    vi
    vn
    cE
    cF
    @5
    cH
    @1
    cN
    cW
    va
    vb
    knoppndvlem22.t
    knoppndvlem22.f
    knoppndvlem22.w
    @5
    eqid
    wph
    cC
    c1
    cneg
    c1
    cioo
    co
    wcel
    @12
    knoppndvlem22.c
    adantr
    wph
    cD
    crp
    wcel
    @12
    knoppndvlem22.d
    adantr
    wph
    cE
    crp
    wcel
    @12
    knoppndvlem22.e
    adantr
    wph
    cH
    cr
    wcel
    @12
    knoppndvlem22.h
    adantr
    wph
    @11
    @7
    simprl
    wph
    cN
    cn
    wcel
    @12
    knoppndvlem22.n
    adantr
    wph
    c1
    cN
    @3
    cmul
    co
    clt
    wbr
    @12
    knoppndvlem22.1
    adantr
    wph
    @11
    @2
    @6
    simprrl
    wph
    @11
    @2
    @6
    simprrr
    knoppndvlem21
    rexlimddv
end
