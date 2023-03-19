include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
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
include "cio.mm"
include "cid.mm"
include "cdif.mm"
include "simpr.mm"
include "sygbasnfpfi.mm"
include "psgneldm.mm"
include "sylanbrc.mm"
include "psgnval.mm"
include "syl.mm"

theorem psgnvalfi
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vx: setvar x
  let vp: setvar p
  assume psgnfvalfi.g: |- G = ( SymGrp ` D )
  assume psgnfvalfi.b: |- B = ( Base ` G )
  assume psgnfvalfi.t: |- T = ran ( pmTrsp ` D )
  assume psgnfvalfi.n: |- N = ( pmSgn ` D )

  disjoint s w
  disjoint D s
  disjoint D w
  disjoint T w
  disjoint G s
  disjoint G w
  disjoint N s
  disjoint N w
  disjoint P s
  disjoint P w
  disjoint T s
  disjoint D x
  disjoint P x
  disjoint s x
  disjoint w x
  disjoint B p
  disjoint B x
  disjoint p x
  disjoint D p
  disjoint p s
  disjoint p w
  assert |- ( ( D e. Fin /\ P e. B ) -> ( N ` P ) = ( iota s E. w e. Word T ( P = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) )

  proof
    cD
    cfn
    wcel
    #
    cP
    cB
    wcel
    #
    wa
    #
    cP
    cN
    cdm
    wcel
    #
    cP
    cN
    cfv
    cP
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
    wceq
    @2
    @1
    cP
    cid
    cdif
    cdm
    cfn
    wcel
    @3
    @0
    @1
    simpr
    cB
    cD
    cP
    cG
    psgnfvalfi.g
    psgnfvalfi.b
    sygbasnfpfi
    cB
    cD
    cP
    cG
    cN
    psgnfvalfi.g
    psgnfvalfi.n
    psgnfvalfi.b
    psgneldm
    sylanbrc
    vw
    cD
    cP
    cT
    cG
    cN
    vs
    psgnfvalfi.g
    psgnfvalfi.t
    psgnfvalfi.n
    psgnval
    syl
end
