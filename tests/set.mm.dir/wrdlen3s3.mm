include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "cs3.mm"
include "wrd3tpop.mm"
include "cvv.mm"
include "fvex.mm"
include "w3a.mm"
include "s3tpop.mm"
include "eqcomd.mm"
include "mp3an.mm"
include "syl6eq.mm"

theorem wrdlen3s3
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ ( # ` W ) = 3 ) -> W = <" ( W ` 0 ) ( W ` 1 ) ( W ` 2 ) "> )

  proof
    cW
    cV
    cword
    wcel
    cW
    chash
    cfv
    c3
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
    c2
    c2
    cW
    cfv
    #
    cop
    ctp
    #
    @0
    @1
    @2
    cs3
    #
    cV
    cW
    wrd3tpop
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @3
    @4
    wceq
    cc0
    cW
    fvex
    c1
    cW
    fvex
    c2
    cW
    fvex
    @5
    @6
    @7
    w3a
    @4
    @3
    @0
    @1
    @2
    cvv
    s3tpop
    eqcomd
    mp3an
    syl6eq
end
