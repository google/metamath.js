include "cv.mm"
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
include "cdm.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "iotabidv.mm"
include "cbs.mm"
include "eqid.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "wcel.mm"
include "crab.mm"
include "wfn.mm"
include "psgnfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "psgnfval.mm"
include "iotaex.mm"
include "fvmpt.mm"

theorem psgnval
  let vw: setvar w
  let cD: class D
  let cP: class P
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vp: setvar p
  let cV: class V
  let cW: class W
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )

  disjoint s w
  disjoint G s
  disjoint G w
  disjoint N s
  disjoint N w
  disjoint P s
  disjoint P w
  disjoint T s
  disjoint T w
  disjoint D s
  disjoint D w
  disjoint s t
  disjoint s x
  disjoint t w
  disjoint t x
  disjoint G t
  disjoint w x
  disjoint G x
  disjoint N t
  disjoint N x
  disjoint P t
  disjoint P x
  disjoint T t
  disjoint T x
  disjoint p s
  disjoint p t
  disjoint D t
  disjoint p w
  disjoint D p
  disjoint G p
  disjoint T p
  disjoint V s
  disjoint V p
  disjoint W s
  disjoint W w
  assert |- ( P e. dom N -> ( N ` P ) = ( iota s E. w e. Word T ( P = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) )

  proof
    vt
    cP
    vt
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
    @1
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
    cP
    @2
    wceq
    #
    @4
    wa
    #
    vw
    @6
    wrex
    #
    vs
    cio
    cN
    cdm
    #
    cN
    @0
    cP
    wceq
    #
    @7
    @10
    vs
    @12
    @5
    @9
    vw
    @6
    @12
    @3
    @8
    @4
    @0
    cP
    @2
    eqeq1
    anbi1d
    rexbidv
    iotabidv
    vt
    vw
    cG
    cbs
    cfv
    #
    cD
    cT
    @11
    cG
    cN
    vs
    vx
    psgnval.g
    @13
    eqid
    #
    cN
    vx
    cv
    cid
    cdif
    cdm
    cfn
    wcel
    vx
    @13
    crab
    #
    wfn
    @11
    @15
    wceq
    @13
    cD
    @15
    cG
    cN
    vx
    psgnval.g
    @14
    @15
    eqid
    psgnval.n
    psgnfn
    @15
    cN
    fndm
    ax-mp
    psgnval.t
    psgnval.n
    psgnfval
    @10
    vs
    iotaex
    fvmpt
end
