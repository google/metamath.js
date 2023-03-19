include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "wss.mm"
include "cc.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "ccncf.mm"
include "wf.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "simprd.mm"
include "knoppcn.mm"
include "cncff.mm"
include "syl.mm"
include "ssid.mm"
include "dvbss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "jca.mm"
include "cle.mm"
include "cmin.mm"
include "wne.mm"
include "cdiv.mm"
include "w3a.mm"
include "wrex.mm"
include "crp.mm"
include "cneg.mm"
include "cioo.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simprl.mm"
include "simplr.mm"
include "cn.mm"
include "cmul.mm"
include "knoppndvlem22.mm"
include "ralrimivva.mm"
include "unbdqndv2.mm"
include "pm2.01da.mm"
include "alrimiv.mm"
include "eq0.mm"
include "sylibr.mm"

theorem knoppndv
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
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vh: setvar h
  assume knoppndv.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppndv.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppndv.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppndv.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndv.n: |- ( ph -> N e. NN )
  assume knoppndv.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )

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
  disjoint F i
  disjoint F w
  disjoint N i
  disjoint N n
  disjoint N w
  disjoint N y
  disjoint N x
  disjoint i x
  disjoint w x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph y
  disjoint N a
  disjoint N b
  disjoint a b
  disjoint W a
  disjoint W b
  disjoint W d
  disjoint W e
  disjoint W h
  disjoint a d
  disjoint a e
  disjoint a h
  disjoint b d
  disjoint b e
  disjoint b h
  disjoint d e
  disjoint d h
  disjoint e h
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint e ph
  disjoint h ph
  disjoint d i
  disjoint d n
  disjoint d w
  disjoint d y
  disjoint e i
  disjoint e n
  disjoint e w
  disjoint e y
  disjoint h i
  disjoint h n
  disjoint h w
  disjoint h y
  assert |- ( ph -> dom ( RR _D W ) = (/) )

  proof
    wph
    vh
    cv
    #
    cr
    cW
    cdv
    co
    cdm
    #
    wcel
    #
    wn
    #
    vh
    wal
    @1
    c0
    wceq
    wph
    @3
    vh
    wph
    @2
    wph
    @2
    wa
    #
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @3
    @4
    wph
    @5
    wph
    @2
    simpl
    @4
    @1
    cr
    @0
    wph
    @1
    cr
    wss
    @2
    wph
    cr
    cr
    cW
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
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
    knoppndv.t
    knoppndv.f
    knoppndv.w
    knoppndv.n
    wph
    cC
    cr
    wcel
    #
    cC
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wph
    cC
    knoppndv.c
    knoppndvlem3
    #
    simpld
    wph
    @8
    @10
    @11
    simprd
    knoppcn
    cr
    cc
    cW
    cncff
    syl
    #
    cr
    cr
    wss
    #
    wph
    cr
    ssid
    #
    a1i
    dvbss
    adantr
    wph
    @2
    simpr
    sseldd
    jca
    @6
    va
    vb
    @0
    cW
    cr
    ve
    vd
    @13
    @6
    @14
    a1i
    wph
    @7
    @5
    @12
    adantr
    @6
    va
    cv
    #
    @0
    cle
    wbr
    @0
    vb
    cv
    #
    cle
    wbr
    wa
    @16
    @15
    cmin
    co
    #
    vd
    cv
    #
    clt
    wbr
    @15
    @16
    wne
    wa
    ve
    cv
    #
    @16
    cW
    cfv
    @15
    cW
    cfv
    cmin
    co
    cabs
    cfv
    @17
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
    ve
    vd
    crp
    crp
    @6
    @19
    crp
    wcel
    #
    @18
    crp
    wcel
    #
    wa
    #
    wa
    vx
    vy
    vw
    cC
    @18
    cT
    vi
    vn
    @19
    cF
    @0
    cN
    cW
    va
    vb
    knoppndv.t
    knoppndv.f
    knoppndv.w
    wph
    cC
    c1
    cneg
    c1
    cioo
    co
    wcel
    @5
    @22
    knoppndv.c
    ad2antrr
    @6
    @20
    @21
    simprr
    @6
    @20
    @21
    simprl
    wph
    @5
    @22
    simplr
    wph
    cN
    cn
    wcel
    @5
    @22
    knoppndv.n
    ad2antrr
    wph
    c1
    cN
    @9
    cmul
    co
    clt
    wbr
    @5
    @22
    knoppndv.1
    ad2antrr
    knoppndvlem22
    ralrimivva
    unbdqndv2
    syl
    pm2.01da
    alrimiv
    vh
    @1
    eq0
    sylibr
end
