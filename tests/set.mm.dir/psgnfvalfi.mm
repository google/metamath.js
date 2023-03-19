include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "cio.mm"
include "cmpt.mm"
include "eqid.mm"
include "psgnfval.mm"
include "wral.mm"
include "sygbasnfpfi.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "mpteq1d.mm"
include "syl5eq.mm"

theorem psgnfvalfi
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let cP: class P
  let vp: setvar p
  assume psgnfvalfi.g: |- G = ( SymGrp ` D )
  assume psgnfvalfi.b: |- B = ( Base ` G )
  assume psgnfvalfi.t: |- T = ran ( pmTrsp ` D )
  assume psgnfvalfi.n: |- N = ( pmSgn ` D )

  disjoint D x
  disjoint s x
  disjoint w x
  disjoint s w
  disjoint B x
  disjoint D s
  disjoint D w
  disjoint T w
  disjoint P x
  disjoint B p
  disjoint p x
  disjoint D p
  disjoint p s
  disjoint p w
  assert |- ( D e. Fin -> N = ( x e. B |-> ( iota s E. w e. Word T ( x = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) ) )

  proof
    cD
    cfn
    wcel
    #
    cN
    vx
    vp
    cv
    #
    cid
    cdif
    cdm
    cfn
    wcel
    #
    vp
    cB
    crab
    #
    vx
    cv
    cG
    vw
    cv
    #
    cgsu
    co
    wceq
    vs
    cv
    c1
    cneg
    @4
    chash
    cfv
    cexp
    co
    wceq
    wa
    vw
    cT
    cword
    wrex
    vs
    cio
    #
    cmpt
    vx
    cB
    @5
    cmpt
    vx
    vw
    cB
    cD
    cT
    @3
    cG
    cN
    vs
    vp
    psgnfvalfi.g
    psgnfvalfi.b
    @3
    eqid
    psgnfvalfi.t
    psgnfvalfi.n
    psgnfval
    @0
    vx
    @3
    cB
    @5
    @0
    cB
    @3
    @0
    @2
    vp
    cB
    wral
    cB
    @3
    wceq
    @0
    @2
    vp
    cB
    cB
    cD
    @1
    cG
    psgnfvalfi.g
    psgnfvalfi.b
    sygbasnfpfi
    ralrimiva
    @2
    vp
    cB
    rabid2
    sylibr
    eqcomd
    mpteq1d
    syl5eq
end
