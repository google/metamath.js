include "caddc.mm"
include "cof.mm"
include "cn0.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "culm.mm"
include "wbr.mm"
include "wex.mm"
include "cdm.mm"
include "wcel.mm"
include "knoppcnlem6.mm"
include "seqex.mm"
include "eldm.mm"
include "sylib.mm"
include "wa.mm"
include "simpr.mm"
include "csu.mm"
include "wceq.mm"
include "cc.mm"
include "ulmcl.mm"
include "feqmptd.mm"
include "adantl.mm"
include "nn0uz.mm"
include "0zd.mm"
include "eqidd.mm"
include "cn.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "knoppcnlem3.mm"
include "adantllr.mm"
include "recnd.mm"
include "cvv.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "knoppcnlem8.mm"
include "a1i.mm"
include "knoppcnlem7.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "adantr.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "eqtrd.mm"
include "ulmclm.mm"
include "isumclim.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem knoppcnlem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vv: setvar v
  assume knoppcnlem9.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem9.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem9.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )
  assume knoppcnlem9.n: |- ( ph -> N e. NN )
  assume knoppcnlem9.1: |- ( ph -> C e. RR )
  assume knoppcnlem9.2: |- ( ph -> ( abs ` C ) < 1 )

  disjoint C m
  disjoint C n
  disjoint C y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint F i
  disjoint F m
  disjoint F w
  disjoint F z
  disjoint i m
  disjoint i w
  disjoint i z
  disjoint m w
  disjoint m z
  disjoint w z
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint i ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint n ph
  disjoint ph y
  disjoint i n
  disjoint i y
  disjoint n w
  disjoint n z
  disjoint w y
  disjoint y z
  disjoint i x
  disjoint m x
  disjoint w x
  disjoint x z
  disjoint F f
  disjoint f i
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint F k
  disjoint F v
  disjoint f k
  disjoint f v
  disjoint k m
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint m v
  disjoint v w
  disjoint v z
  disjoint W f
  disjoint f ph
  disjoint k ph
  disjoint ph v
  assert |- ( ph -> seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) ) ( ~~>u ` RR ) W )

  proof
    wph
    caddc
    cof
    #
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
    #
    cc0
    cseq
    #
    vf
    cv
    #
    cr
    culm
    cfv
    #
    wbr
    #
    vf
    wex
    #
    @2
    cW
    @4
    wbr
    #
    wph
    @2
    @4
    cdm
    wcel
    @6
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
    knoppcnlem9.t
    knoppcnlem9.f
    knoppcnlem9.n
    knoppcnlem9.1
    knoppcnlem9.2
    knoppcnlem6
    vf
    @2
    @4
    @0
    @1
    cc0
    seqex
    eldm
    sylib
    wph
    @5
    @7
    vf
    wph
    @5
    @7
    wph
    @5
    wa
    #
    @2
    @3
    cW
    @4
    wph
    @5
    simpr
    @8
    @3
    vw
    cr
    vw
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    vw
    cr
    cn0
    vi
    cv
    #
    @9
    cF
    cfv
    #
    cfv
    #
    vi
    csu
    #
    cmpt
    #
    cW
    @5
    @3
    @11
    wceq
    wph
    @5
    vw
    cr
    cc
    @3
    cr
    @2
    @3
    ulmcl
    feqmptd
    adantl
    @8
    vw
    cr
    @10
    @15
    @8
    @9
    cr
    wcel
    #
    wa
    #
    @15
    @10
    @18
    @14
    @10
    vi
    @13
    cc0
    cn0
    nn0uz
    @18
    0zd
    #
    @18
    @12
    cn0
    wcel
    #
    wa
    #
    @14
    eqidd
    @21
    @14
    wph
    @17
    @20
    @14
    cr
    wcel
    @5
    wph
    @17
    wa
    #
    @20
    wa
    vx
    vy
    @9
    cC
    cT
    vn
    cF
    @12
    cN
    knoppcnlem9.t
    knoppcnlem9.f
    wph
    cN
    cn
    wcel
    #
    @17
    @20
    knoppcnlem9.n
    ad2antrr
    wph
    cC
    cr
    wcel
    #
    @17
    @20
    knoppcnlem9.1
    ad2antrr
    wph
    @17
    @20
    simplr
    @22
    @20
    simpr
    knoppcnlem3
    adantllr
    recnd
    @18
    @9
    cr
    vk
    @2
    @3
    caddc
    @13
    cc0
    cseq
    #
    cc0
    cvv
    cn0
    nn0uz
    @19
    wph
    cn0
    cc
    cr
    cmap
    co
    @2
    wf
    @5
    @17
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
    knoppcnlem9.t
    knoppcnlem9.f
    knoppcnlem9.n
    knoppcnlem9.1
    knoppcnlem8
    ad2antrr
    @8
    @17
    simpr
    #
    @25
    cvv
    wcel
    @18
    caddc
    @13
    cc0
    seqex
    a1i
    @18
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @9
    @27
    @2
    cfv
    #
    cfv
    @9
    vv
    cr
    @27
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
    @27
    @25
    cfv
    #
    @29
    @9
    @30
    @35
    wph
    @17
    @28
    @30
    @35
    wceq
    @5
    @22
    @28
    wa
    vx
    vy
    vz
    vv
    cC
    cT
    vm
    vn
    cF
    @27
    cN
    knoppcnlem9.t
    knoppcnlem9.f
    wph
    @23
    @17
    @28
    knoppcnlem9.n
    ad2antrr
    wph
    @24
    @17
    @28
    knoppcnlem9.1
    ad2antrr
    @22
    @28
    simpr
    knoppcnlem7
    adantllr
    fveq1d
    @29
    vv
    @9
    @34
    @36
    cr
    @35
    cvv
    @35
    @35
    wceq
    @29
    @35
    eqid
    a1i
    @31
    @9
    wceq
    #
    @34
    @36
    wceq
    @29
    @37
    @27
    @33
    @25
    @37
    @32
    @13
    caddc
    cc0
    @31
    @9
    cF
    fveq2
    seqeq3d
    fveq1d
    adantl
    @18
    @17
    @28
    @26
    adantr
    @29
    @27
    @25
    fvexd
    fvmptd
    eqtrd
    wph
    @5
    @17
    simplr
    ulmclm
    isumclim
    eqcomd
    mpteq2dva
    @8
    cW
    @16
    cW
    @16
    wceq
    @8
    knoppcnlem9.w
    a1i
    eqcomd
    3eqtrd
    breqtrd
    ex
    exlimdv
    mpd
end
