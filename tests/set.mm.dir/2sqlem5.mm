include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cmul.mm"
include "wcel.mm"
include "2sqlem2.mm"
include "sylib.mm"
include "wa.mm"
include "reeanv.mm"
include "cn.mm"
include "ad2antrr.mm"
include "cprime.mm"
include "simplrr.mm"
include "simprlr.mm"
include "simplrl.mm"
include "simprll.mm"
include "simprrr.mm"
include "simprrl.mm"
include "2sqlem4.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem 2sqlem5
  let wph: wff ph
  let vw: setvar w
  let cP: class P
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cA: class A
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let cM: class M
  let cD: class D
  let cE: class E
  let cY: class Y
  let cF: class F
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem5.1: |- ( ph -> N e. NN )
  assume 2sqlem5.2: |- ( ph -> P e. Prime )
  assume 2sqlem5.3: |- ( ph -> ( N x. P ) e. S )
  assume 2sqlem5.4: |- ( ph -> P e. S )


  assert |- ( ph -> N e. S )

  proof
    wph
    cP
    vp
    cv
    #
    c2
    cexp
    co
    vq
    cv
    #
    c2
    cexp
    co
    caddc
    co
    wceq
    #
    vq
    cz
    wrex
    #
    vp
    cz
    wrex
    #
    cN
    cP
    cmul
    co
    #
    vx
    cv
    #
    c2
    cexp
    co
    vy
    cv
    #
    c2
    cexp
    co
    caddc
    co
    wceq
    #
    vy
    cz
    wrex
    #
    vx
    cz
    wrex
    #
    cN
    cS
    wcel
    #
    wph
    cP
    cS
    wcel
    @4
    2sqlem5.4
    vp
    vq
    vw
    cP
    cS
    2sq.1
    2sqlem2
    sylib
    wph
    @5
    cS
    wcel
    @10
    2sqlem5.3
    vx
    vy
    vw
    @5
    cS
    2sq.1
    2sqlem2
    sylib
    @4
    @10
    wa
    @3
    @9
    wa
    #
    vx
    cz
    wrex
    vp
    cz
    wrex
    wph
    @11
    @3
    @9
    vp
    vx
    cz
    cz
    reeanv
    wph
    @12
    @11
    vp
    vx
    cz
    cz
    @12
    @2
    @8
    wa
    #
    vy
    cz
    wrex
    vq
    cz
    wrex
    wph
    @0
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    wa
    #
    @11
    @2
    @8
    vq
    vy
    cz
    cz
    reeanv
    @17
    @13
    @11
    vq
    vy
    cz
    cz
    @17
    @1
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    wa
    #
    @13
    @11
    @17
    @20
    @13
    wa
    #
    wa
    vw
    @6
    @7
    @0
    @1
    cP
    cS
    cN
    2sq.1
    wph
    cN
    cn
    wcel
    @16
    @21
    2sqlem5.1
    ad2antrr
    wph
    cP
    cprime
    wcel
    @16
    @21
    2sqlem5.2
    ad2antrr
    wph
    @14
    @15
    @21
    simplrr
    @17
    @18
    @19
    @13
    simprlr
    wph
    @14
    @15
    @21
    simplrl
    @17
    @18
    @19
    @13
    simprll
    @17
    @20
    @2
    @8
    simprrr
    @17
    @20
    @2
    @8
    simprrl
    2sqlem4
    expr
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
end
