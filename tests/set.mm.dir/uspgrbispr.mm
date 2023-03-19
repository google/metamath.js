include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "c2nd.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "uspgrex.mm"
include "mptexd.mm"
include "eqid.mm"
include "uspgrsprf1o.mm"
include "f1oeq1.mm"
include "elabd.mm"

theorem uspgrbispr
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vf: setvar f
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
  disjoint G f
  disjoint P f
  disjoint G g
  disjoint P g
  disjoint e g
  disjoint g v
  disjoint f g
  disjoint k x
  assert |- ( V e. W -> E. f f : G -1-1-onto-> P )

  proof
    cV
    cW
    wcel
    #
    cG
    cP
    vf
    cv
    #
    wf1o
    cG
    cP
    vg
    cG
    vg
    cv
    c2nd
    cfv
    #
    cmpt
    #
    wf1o
    vf
    @3
    @0
    vg
    cG
    @2
    cvv
    vv
    cP
    ve
    cG
    cV
    cW
    vq
    uspgrsprf.p
    uspgrsprf.g
    uspgrex
    mptexd
    vv
    cP
    ve
    vg
    @3
    cG
    cV
    cW
    vq
    uspgrsprf.p
    uspgrsprf.g
    @3
    eqid
    uspgrsprf1o
    cG
    cP
    @1
    @3
    f1oeq1
    elabd
end
