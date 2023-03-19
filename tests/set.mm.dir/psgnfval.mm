include "cpsgn.mm"
include "cfv.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "cio.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "csymg.mm"
include "cbs.mm"
include "crab.mm"
include "cpmtr.mm"
include "crn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "rabeq.mm"
include "syl.mm"
include "rneqd.mm"
include "wrdeq.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "rexeqbidv.mm"
include "iotabidv.mm"
include "mpteq12dv.mm"
include "df-psgn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex2.mm"
include "mptex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "base0.mm"
include "rab0.mm"
include "syl6eq.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem psgnfval
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vp: setvar p
  let vd: setvar d
  assume psgnfval.g: |- G = ( SymGrp ` D )
  assume psgnfval.b: |- B = ( Base ` G )
  assume psgnfval.f: |- F = { p e. B | dom ( p \ _I ) e. Fin }
  assume psgnfval.t: |- T = ran ( pmTrsp ` D )
  assume psgnfval.n: |- N = ( pmSgn ` D )

  disjoint p s
  disjoint p w
  disjoint p x
  disjoint s w
  disjoint s x
  disjoint w x
  disjoint D s
  disjoint D w
  disjoint D x
  disjoint F x
  disjoint T w
  disjoint B p
  disjoint d p
  disjoint d s
  disjoint d w
  disjoint d x
  disjoint D d
  disjoint F d
  disjoint G d
  disjoint T d
  assert |- N = ( x e. F |-> ( iota s E. w e. Word T ( x = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) )

  proof
    cN
    cD
    cpsgn
    cfv
    #
    vx
    cF
    vx
    cv
    #
    cG
    vw
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vs
    cv
    c1
    cneg
    @2
    chash
    cfv
    cexp
    co
    wceq
    #
    wa
    #
    vw
    cT
    cword
    #
    wrex
    #
    vs
    cio
    #
    cmpt
    #
    psgnfval.n
    cD
    cvv
    wcel
    #
    @0
    @10
    wceq
    vd
    cD
    vx
    vp
    cv
    cid
    cdif
    cdm
    cfn
    wcel
    #
    vp
    vd
    cv
    #
    csymg
    cfv
    #
    cbs
    cfv
    #
    crab
    #
    @1
    @14
    @2
    cgsu
    co
    #
    wceq
    #
    @5
    wa
    #
    vw
    @13
    cpmtr
    cfv
    #
    crn
    #
    cword
    #
    wrex
    #
    vs
    cio
    #
    cmpt
    @10
    cvv
    cpsgn
    @13
    cD
    wceq
    #
    vx
    @16
    @24
    cF
    @9
    @25
    @16
    @12
    vp
    cB
    crab
    #
    cF
    @25
    @15
    cB
    wceq
    @16
    @26
    wceq
    @25
    @15
    cG
    cbs
    cfv
    #
    cB
    @25
    @14
    cG
    cbs
    @25
    @14
    cD
    csymg
    cfv
    #
    cG
    @13
    cD
    csymg
    fveq2
    psgnfval.g
    syl6eqr
    #
    fveq2d
    psgnfval.b
    syl6eqr
    @12
    vp
    @15
    cB
    rabeq
    syl
    psgnfval.f
    syl6eqr
    @25
    @23
    @8
    vs
    @25
    @19
    @6
    vw
    @22
    @7
    @25
    @21
    cT
    wceq
    @22
    @7
    wceq
    @25
    @21
    cD
    cpmtr
    cfv
    #
    crn
    cT
    @25
    @20
    @30
    @13
    cD
    cpmtr
    fveq2
    rneqd
    psgnfval.t
    syl6eqr
    @21
    cT
    wrdeq
    syl
    @25
    @18
    @4
    @5
    @25
    @17
    @3
    @1
    @25
    @14
    cG
    @2
    cgsu
    @29
    oveq1d
    eqeq2d
    anbi1d
    rexeqbidv
    iotabidv
    mpteq12dv
    vx
    vw
    vs
    vp
    vd
    df-psgn
    vx
    cF
    @9
    @12
    vp
    cB
    cF
    psgnfval.f
    cB
    @27
    cvv
    psgnfval.b
    cG
    cbs
    fvex
    eqeltri
    rabex2
    mptex
    fvmpt
    @11
    wn
    #
    @0
    c0
    @10
    cD
    cpsgn
    fvprc
    @31
    @10
    vx
    c0
    @9
    cmpt
    c0
    @31
    vx
    cF
    c0
    @9
    @31
    cF
    @26
    c0
    psgnfval.f
    @31
    @26
    @12
    vp
    c0
    crab
    #
    c0
    @31
    cB
    c0
    wceq
    @26
    @32
    wceq
    @31
    cB
    @27
    c0
    psgnfval.b
    @31
    @27
    c0
    cbs
    cfv
    c0
    @31
    cG
    c0
    cbs
    @31
    cG
    @28
    c0
    psgnfval.g
    cD
    csymg
    fvprc
    syl5eq
    fveq2d
    base0
    syl6eqr
    syl5eq
    @12
    vp
    cB
    c0
    rabeq
    syl
    @12
    vp
    rab0
    syl6eq
    syl5eq
    mpteq1d
    vx
    @9
    mpt0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
