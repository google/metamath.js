include "crp.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "csqrt.mm"
include "cmul.mm"
include "c1.mm"
include "cr.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "divsqrsumf.mm"
include "ffvelrni.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "rpsup.mm"
include "cmpt.mm"
include "crli.mm"
include "wf.mm"
include "feqmptd.mm"
include "eqbrtrrd.mm"
include "adantl.mm"
include "rlimrecl.mm"
include "resubcl.mm"
include "syl2anr.mm"
include "recnd.mm"
include "rpsqrtcl.mm"
include "rpcnd.mm"
include "mulcld.mm"
include "1red.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "absmuld.mm"
include "cc0.mm"
include "rprege0d.mm"
include "absid.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cdiv.mm"
include "divsqrtsum2.mm"
include "abscld.mm"
include "lemuldivd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "adantrr.mm"
include "elo1d.mm"

theorem divsqrtsumo1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cL: class L
  let cA: class A
  assume divsqrtsum.2: |- F = ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( 1 / ( sqrt ` n ) ) - ( 2 x. ( sqrt ` x ) ) ) )
  assume divsqrsum2.1: |- ( ph -> F ~~>r L )

  disjoint x y
  disjoint F y
  disjoint L y
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint n x
  disjoint A n
  disjoint A x
  assert |- ( ph -> ( y e. RR+ |-> ( ( ( F ` y ) - L ) x. ( sqrt ` y ) ) ) e. O(1) )

  proof
    wph
    vy
    crp
    vy
    cv
    #
    cF
    cfv
    #
    cL
    cmin
    co
    #
    @0
    csqrt
    cfv
    #
    cmul
    co
    #
    c1
    c1
    crp
    cr
    wss
    wph
    rpssre
    a1i
    wph
    @0
    crp
    wcel
    #
    wa
    #
    @2
    @3
    @6
    @2
    @5
    @1
    cr
    wcel
    #
    cL
    cr
    wcel
    @2
    cr
    wcel
    wph
    crp
    cr
    @0
    cF
    vx
    vn
    cF
    divsqrtsum.2
    divsqrsumf
    #
    ffvelrni
    #
    wph
    vy
    crp
    @1
    cL
    crp
    cxr
    clt
    csup
    cpnf
    wceq
    wph
    rpsup
    a1i
    wph
    cF
    vy
    crp
    @1
    cmpt
    cL
    crli
    wph
    vy
    crp
    cr
    cF
    crp
    cr
    cF
    wf
    wph
    @8
    a1i
    feqmptd
    divsqrsum2.1
    eqbrtrrd
    @5
    @7
    wph
    @9
    adantl
    rlimrecl
    @1
    cL
    resubcl
    syl2anr
    recnd
    #
    @6
    @3
    @5
    @3
    crp
    wcel
    wph
    @0
    rpsqrtcl
    adantl
    #
    rpcnd
    #
    mulcld
    wph
    1red
    #
    @13
    wph
    @5
    @4
    cabs
    cfv
    #
    c1
    cle
    wbr
    c1
    @0
    cle
    wbr
    @6
    @14
    @2
    cabs
    cfv
    #
    @3
    cmul
    co
    #
    c1
    cle
    @6
    @14
    @15
    @3
    cabs
    cfv
    #
    cmul
    co
    @16
    @6
    @2
    @3
    @10
    @12
    absmuld
    @6
    @17
    @3
    @15
    cmul
    @6
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    wa
    @17
    @3
    wceq
    @6
    @3
    @11
    rprege0d
    @3
    absid
    syl
    oveq2d
    eqtrd
    @6
    @16
    c1
    cle
    wbr
    @15
    c1
    @3
    cdiv
    co
    cle
    wbr
    wph
    vx
    @0
    vn
    cF
    cL
    divsqrtsum.2
    divsqrsum2.1
    divsqrtsum2
    @6
    @15
    c1
    @3
    @6
    @2
    @10
    abscld
    @6
    1red
    @11
    lemuldivd
    mpbird
    eqbrtrd
    adantrr
    elo1d
end
