include "cr.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "eqidd.mm"
include "cn.mm"
include "adantr.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "simpr.mm"
include "knoppcnlem3.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sumeq2sdv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "knoppndvlem4.mm"
include "seqex.mm"
include "fvex.mm"
include "breldm.mm"
include "syl.mm"
include "isumrecl.mm"
include "fmptd.mm"

theorem knoppf
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
  let vz: setvar z
  assume knoppf.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppf.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppf.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppf.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppf.n: |- ( ph -> N e. NN )

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
  disjoint F z
  disjoint i z
  disjoint w z
  disjoint ph z
  disjoint n z
  disjoint y z
  disjoint x z
  assert |- ( ph -> W : RR --> RR )

  proof
    wph
    vw
    cr
    cn0
    vi
    cv
    #
    vw
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cr
    cW
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @3
    vi
    @2
    cc0
    cn0
    nn0uz
    @6
    0zd
    @6
    @0
    cn0
    wcel
    #
    wa
    #
    @3
    eqidd
    @8
    vx
    vy
    @1
    cC
    cT
    vn
    cF
    @0
    cN
    knoppf.t
    knoppf.f
    @6
    cN
    cn
    wcel
    #
    @7
    wph
    @9
    @5
    knoppf.n
    adantr
    #
    adantr
    @6
    cC
    cr
    wcel
    #
    @7
    wph
    @11
    @5
    wph
    @11
    cC
    cabs
    cfv
    c1
    clt
    wbr
    wph
    cC
    knoppf.c
    knoppndvlem3
    simpld
    adantr
    adantr
    @6
    @5
    @7
    wph
    @5
    simpr
    #
    adantr
    @6
    @7
    simpr
    knoppcnlem3
    @6
    caddc
    @2
    cc0
    cseq
    #
    @1
    cW
    cfv
    #
    cli
    wbr
    @13
    cli
    cdm
    wcel
    @6
    vx
    vy
    vz
    @1
    cC
    cT
    vi
    vn
    cF
    cN
    cW
    knoppf.t
    knoppf.f
    cW
    vw
    cr
    @4
    cmpt
    vz
    cr
    cn0
    @0
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmpt
    knoppf.w
    vw
    vz
    cr
    @4
    @18
    @1
    @15
    wceq
    #
    cn0
    @3
    @17
    vi
    @19
    @0
    @2
    @16
    @1
    @15
    cF
    fveq2
    fveq1d
    sumeq2sdv
    cbvmptv
    eqtri
    @12
    wph
    cC
    c1
    cneg
    c1
    cioo
    co
    wcel
    @5
    knoppf.c
    adantr
    @10
    knoppndvlem4
    @13
    @14
    cli
    caddc
    @2
    cc0
    seqex
    @1
    cW
    fvex
    breldm
    syl
    isumrecl
    knoppf.w
    fmptd
end
