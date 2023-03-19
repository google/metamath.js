include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cpsgn.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "cword.mm"
include "wrex.mm"
include "weu.mm"
include "cid.mm"
include "cdif.mm"
include "simpr.mm"
include "sygbasnfpfi.mm"
include "eqid.mm"
include "psgneldm.mm"
include "sylanbrc.mm"
include "psgneu.mm"
include "syl.mm"

theorem psgnfieu
  let vw: setvar w
  let cB: class B
  let cQ: class Q
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  assume psgnfitr.g: |- G = ( SymGrp ` N )
  assume psgnfitr.p: |- B = ( Base ` G )
  assume psgnfitr.t: |- T = ran ( pmTrsp ` N )

  disjoint G w
  disjoint Q w
  disjoint T w
  disjoint G s
  disjoint N s
  disjoint N w
  disjoint s w
  disjoint Q s
  disjoint T s
  assert |- ( ( N e. Fin /\ Q e. B ) -> E! s E. w e. Word T ( Q = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cQ
    cB
    wcel
    #
    wa
    #
    cQ
    cN
    cpsgn
    cfv
    #
    cdm
    wcel
    #
    cQ
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
    @5
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
    weu
    @2
    @1
    cQ
    cid
    cdif
    cdm
    cfn
    wcel
    @4
    @0
    @1
    simpr
    cB
    cN
    cQ
    cG
    psgnfitr.g
    psgnfitr.p
    sygbasnfpfi
    cB
    cN
    cQ
    cG
    @3
    psgnfitr.g
    @3
    eqid
    #
    psgnfitr.p
    psgneldm
    sylanbrc
    vw
    cN
    cQ
    cT
    cG
    @3
    vs
    psgnfitr.g
    psgnfitr.t
    @6
    psgneu
    syl
end
