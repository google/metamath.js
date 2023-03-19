include "clvec.mm"
include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "numth3.mm"
include "ax-mp.mm"
include "jctr.mm"
include "lbsextg.mm"
include "syl3an1.mm"

theorem lbsext
  let vx: setvar x
  let cC: class C
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume lbsex.j: |- J = ( LBasis ` W )
  assume lbsex.v: |- V = ( Base ` W )
  assume lbsex.n: |- N = ( LSpan ` W )

  disjoint s x
  disjoint C s
  disjoint C x
  disjoint J s
  disjoint N s
  disjoint N x
  disjoint V s
  disjoint W s
  disjoint W x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J y
  disjoint N y
  disjoint N z
  disjoint V y
  disjoint V z
  disjoint W y
  assert |- ( ( W e. LVec /\ C C_ V /\ A. x e. C -. x e. ( N ` ( C \ { x } ) ) ) -> E. s e. J C C_ s )

  proof
    cW
    clvec
    wcel
    #
    @0
    cV
    cpw
    #
    ccrd
    cdm
    wcel
    #
    wa
    cC
    cV
    wss
    vx
    cv
    #
    cC
    @3
    csn
    cdif
    cN
    cfv
    wcel
    wn
    vx
    cC
    wral
    cC
    vs
    cv
    wss
    vs
    cJ
    wrex
    @0
    @2
    @1
    cvv
    wcel
    @2
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lbsex.v
    cW
    cbs
    fvex
    eqeltri
    pwex
    @1
    cvv
    numth3
    ax-mp
    jctr
    vx
    cC
    cJ
    cN
    cV
    cW
    vs
    lbsex.j
    lbsex.v
    lbsex.n
    lbsextg
    syl3an1
end
