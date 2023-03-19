include "ctop.mm"
include "wcel.mm"
include "wfn.mm"
include "wa.mm"
include "cvv.mm"
include "wfun.mm"
include "cqtop.mm"
include "co.mm"
include "simpl.mm"
include "id.mm"
include "topopn.mm"
include "fnex.mm"
include "syl2anr.mm"
include "fnfun.mm"
include "adantl.mm"
include "qtoptop2.mm"
include "syl3anc.mm"

theorem qtoptop
  let cF: class F
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cY: class Y
  assume qtoptop.1: |- X = U. J


  assert |- ( ( J e. Top /\ F Fn X ) -> ( J qTop F ) e. Top )

  proof
    cJ
    ctop
    wcel
    #
    cF
    cX
    wfn
    #
    wa
    @0
    cF
    cvv
    wcel
    #
    cF
    wfun
    #
    cJ
    cF
    cqtop
    co
    ctop
    wcel
    @0
    @1
    simpl
    @1
    @1
    cX
    cJ
    wcel
    @2
    @0
    @1
    id
    cJ
    cX
    qtoptop.1
    topopn
    cX
    cJ
    cF
    fnex
    syl2anr
    @1
    @3
    @0
    cX
    cF
    fnfun
    adantl
    cF
    cJ
    cvv
    qtoptop2
    syl3anc
end
