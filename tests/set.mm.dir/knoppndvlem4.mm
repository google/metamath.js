include "cr.mm"
include "caddc.mm"
include "cof.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "cvv.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "knoppcnlem8.mm"
include "seqex.mm"
include "a1i.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "simpr.mm"
include "knoppcnlem7.mm"
include "fveq1d.mm"
include "wceq.mm"
include "eqid.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "adantl.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "eqtrd.mm"
include "simprd.mm"
include "knoppcnlem9.mm"
include "ulmclm.mm"

theorem knoppndvlem4
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
  let vk: setvar k
  let vv: setvar v
  let vm: setvar m
  let vz: setvar z
  assume knoppndvlem4.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndvlem4.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndvlem4.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndvlem4.a: |- ( ph -> A e. RR )
  assume knoppndvlem4.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem4.n: |- ( ph -> N e. NN )

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
  disjoint A k
  disjoint A v
  disjoint k v
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
  disjoint F k
  disjoint F v
  disjoint k m
  disjoint k z
  disjoint m v
  disjoint v z
  disjoint W k
  disjoint m ph
  disjoint ph z
  disjoint n z
  disjoint y z
  disjoint m x
  disjoint x z
  disjoint k ph
  disjoint ph v
  assert |- ( ph -> seq 0 ( + , ( F ` A ) ) ~~> ( W ` A ) )

  proof
    wph
    cA
    cr
    vk
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
    #
    cW
    caddc
    cA
    cF
    cfv
    #
    cc0
    cseq
    #
    cc0
    cvv
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
    knoppndvlem4.t
    knoppndvlem4.f
    knoppndvlem4.n
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
    knoppndvlem4.c
    knoppndvlem3
    #
    simpld
    #
    knoppcnlem8
    knoppndvlem4.a
    @2
    cvv
    wcel
    wph
    caddc
    @1
    cc0
    seqex
    a1i
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    cA
    @7
    @0
    cfv
    #
    cfv
    cA
    vv
    cr
    @7
    caddc
    vv
    cv
    #
    cF
    cfv
    #
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    @7
    @2
    cfv
    #
    @9
    cA
    @10
    @15
    @9
    vx
    vy
    vz
    vv
    cC
    cT
    vm
    vn
    cF
    @7
    cN
    knoppndvlem4.t
    knoppndvlem4.f
    wph
    cN
    cn
    wcel
    @8
    knoppndvlem4.n
    adantr
    wph
    @3
    @8
    @6
    adantr
    wph
    @8
    simpr
    knoppcnlem7
    fveq1d
    wph
    @16
    @17
    wceq
    @8
    wph
    vv
    cA
    @14
    @17
    cr
    @15
    cvv
    @15
    @15
    wceq
    wph
    @15
    eqid
    a1i
    @11
    cA
    wceq
    #
    @14
    @17
    wceq
    wph
    @18
    @7
    @13
    @2
    @18
    @12
    @1
    caddc
    cc0
    @11
    cA
    cF
    fveq2
    seqeq3d
    fveq1d
    adantl
    knoppndvlem4.a
    wph
    @7
    @2
    fvexd
    fvmptd
    adantr
    eqtrd
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
    knoppndvlem4.t
    knoppndvlem4.f
    knoppndvlem4.w
    knoppndvlem4.n
    @6
    wph
    @3
    @4
    @5
    simprd
    knoppcnlem9
    ulmclm
end
