include "cv.mm"
include "wfun.mm"
include "wcel.mm"
include "wi.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "bnj1317.mm"
include "nf5i.mm"
include "nfv.mm"
include "nfim.mm"
include "eleq1.mm"
include "funeq.mm"
include "imbi12d.mm"
include "bnj1436.mm"
include "bnj1299.mm"
include "fnfun.mm"
include "bnj31.mm"
include "bnj1265.mm"
include "chvar.mm"
include "rgen.mm"

theorem bnj1497
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1497.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1497.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1497.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }

  disjoint C g
  disjoint d f
  disjoint f g
  assert |- A. g e. C Fun g

  proof
    vg
    cv
    #
    wfun
    #
    vg
    cC
    vf
    cv
    #
    cC
    wcel
    #
    @2
    wfun
    #
    wi
    @0
    cC
    wcel
    #
    @1
    wi
    vf
    vg
    @5
    @1
    vf
    @5
    vf
    @2
    vd
    cv
    #
    wfn
    #
    vx
    cv
    @2
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @6
    wral
    #
    wa
    vd
    cB
    wrex
    #
    vf
    vg
    cC
    bnj1497.3
    bnj1317
    nf5i
    @1
    vf
    nfv
    nfim
    @2
    @0
    wceq
    @3
    @5
    @4
    @1
    @2
    @0
    cC
    eleq1
    @2
    @0
    funeq
    imbi12d
    @3
    @4
    vd
    cB
    @3
    @7
    @4
    vd
    cB
    @3
    @7
    @8
    vd
    cB
    @9
    vf
    cC
    bnj1497.3
    bnj1436
    bnj1299
    @6
    @2
    fnfun
    bnj31
    bnj1265
    chvar
    rgen
end
