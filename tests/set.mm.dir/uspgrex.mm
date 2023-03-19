include "wcel.mm"
include "cvv.mm"
include "cspr.mm"
include "cfv.mm"
include "cpw.mm"
include "fvex.mm"
include "pwex.mm"
include "eqeltri.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wb.mm"
include "eqid.mm"
include "uspgrsprf1o.mm"
include "f1ovv.mm"
include "syl.mm"
include "mpbiri.mm"

theorem uspgrex
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let cG: class G
  let cV: class V
  let cW: class W
  let vq: setvar q
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }

  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint W e
  disjoint W v
  disjoint W q
  disjoint G g
  disjoint P g
  disjoint e g
  disjoint g v
  disjoint k x
  assert |- ( V e. W -> G e. _V )

  proof
    cV
    cW
    wcel
    #
    cG
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    cP
    cV
    cspr
    cfv
    #
    cpw
    cvv
    uspgrsprf.p
    @3
    cV
    cspr
    fvex
    pwex
    eqeltri
    @0
    cG
    cP
    vg
    cG
    vg
    cv
    c2nd
    cfv
    cmpt
    #
    wf1o
    @1
    @2
    wb
    vv
    cP
    ve
    vg
    @4
    cG
    cV
    cW
    vq
    uspgrsprf.p
    uspgrsprf.g
    @4
    eqid
    uspgrsprf1o
    cG
    cP
    @4
    f1ovv
    syl
    mpbiri
end
