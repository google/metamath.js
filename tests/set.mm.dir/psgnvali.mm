include "cdm.mm"
include "wcel.mm"
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
include "cab.mm"
include "cio.mm"
include "psgnval.mm"
include "weu.mm"
include "psgneu.mm"
include "iotacl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylib.mm"

theorem psgnvali
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

  disjoint G w
  disjoint N w
  disjoint P w
  disjoint T w
  disjoint D w
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint G s
  disjoint t w
  disjoint t x
  disjoint G t
  disjoint w x
  disjoint G x
  disjoint N s
  disjoint N t
  disjoint N x
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint T s
  disjoint T t
  disjoint T x
  disjoint p s
  disjoint D s
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
  assert |- ( P e. dom N -> E. w e. Word T ( P = ( G gsum w ) /\ ( N ` P ) = ( -u 1 ^ ( # ` w ) ) ) )

  proof
    cP
    cN
    cdm
    wcel
    #
    cP
    cN
    cfv
    #
    cP
    cG
    vw
    cv
    #
    cgsu
    co
    wceq
    #
    vs
    cv
    #
    c1
    cneg
    @2
    chash
    cfv
    cexp
    co
    #
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
    cab
    #
    wcel
    @3
    @1
    @5
    wceq
    #
    wa
    #
    vw
    @8
    wrex
    #
    @0
    @1
    @9
    vs
    cio
    #
    @10
    vw
    cD
    cP
    cT
    cG
    cN
    vs
    psgnval.g
    psgnval.t
    psgnval.n
    psgnval
    @0
    @9
    vs
    weu
    @14
    @10
    wcel
    vw
    cD
    cP
    cT
    cG
    cN
    vs
    psgnval.g
    psgnval.t
    psgnval.n
    psgneu
    @9
    vs
    iotacl
    syl
    eqeltrd
    @9
    @13
    vs
    @1
    cP
    cN
    fvex
    @4
    @1
    wceq
    #
    @7
    @12
    vw
    @8
    @15
    @6
    @11
    @3
    @4
    @1
    @5
    eqeq1
    anbi2d
    rexbidv
    elab
    sylib
end
