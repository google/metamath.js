include "cword.mm"
include "wcel.mm"
include "cgsu.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cdm.mm"
include "eqid.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "psgneldm2.mm"
include "biimpar.mm"
include "sylan2.mm"

theorem psgneldm2i
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let cP: class P
  let vp: setvar p
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )


  assert |- ( ( D e. V /\ W e. Word T ) -> ( G gsum W ) e. dom N )

  proof
    cW
    cT
    cword
    #
    wcel
    #
    cD
    cV
    wcel
    #
    cG
    cW
    cgsu
    co
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
    vw
    @0
    wrex
    #
    @3
    cN
    cdm
    wcel
    #
    @1
    @3
    @3
    wceq
    #
    @7
    @3
    eqid
    @6
    @9
    vw
    cW
    @0
    @4
    cW
    wceq
    @5
    @3
    @3
    @4
    cW
    cG
    cgsu
    oveq2
    eqeq2d
    rspcev
    mpan2
    @2
    @8
    @7
    vw
    cD
    @3
    cT
    cG
    cN
    cV
    psgnval.g
    psgnval.t
    psgnval.n
    psgneldm2
    biimpar
    sylan2
end
