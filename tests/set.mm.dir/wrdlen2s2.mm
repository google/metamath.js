include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "cs2.mm"
include "wrd2pr2op.mm"
include "cvv.mm"
include "fvex.mm"
include "s2prop.mm"
include "eqcomd.mm"
include "mp2an.mm"
include "syl6eq.mm"

theorem wrdlen2s2
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 2 ) -> W = <" ( W ` 0 ) ( W ` 1 ) "> )

  proof
    cW
    cV
    cword
    wcel
    cW
    chash
    cfv
    c2
    wceq
    wa
    cW
    cc0
    cc0
    cW
    cfv
    #
    cop
    c1
    c1
    cW
    cfv
    #
    cop
    cpr
    #
    @0
    @1
    cs2
    #
    cV
    cW
    wrd2pr2op
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @2
    @3
    wceq
    cc0
    cW
    fvex
    c1
    cW
    fvex
    @4
    @5
    wa
    @3
    @2
    @0
    @1
    cvv
    s2prop
    eqcomd
    mp2an
    syl6eq
end
