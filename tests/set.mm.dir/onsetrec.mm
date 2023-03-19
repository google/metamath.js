include "csetrecs.mm"
include "con0.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "wtru.mm"
include "eqid.mm"
include "cfv.mm"
include "wal.mm"
include "onsetreclem2.mm"
include "ax-gen.mm"
include "a1i.mm"
include "setrec2v.mm"
include "trud.mm"
include "cvv.mm"
include "vex.mm"
include "id.mm"
include "setrec1.mm"
include "onsetreclem3.mm"
include "ssel.mm"
include "syl2im.mm"
include "com12.mm"
include "rgen.mm"
include "tfi.mm"
include "mp2an.mm"

theorem onsetrec
  let vx: setvar x
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume onsetrec.1: |- F = ( x e. _V |-> { U. x , suc U. x } )


  assert |- setrecs ( F ) = On

  proof
    cF
    csetrecs
    #
    con0
    wss
    #
    va
    cv
    #
    @0
    wss
    #
    @2
    @0
    wcel
    #
    wi
    #
    va
    con0
    wral
    @0
    con0
    wceq
    @1
    wtru
    @0
    con0
    cF
    va
    @0
    eqid
    #
    @2
    con0
    wss
    @2
    cF
    cfv
    #
    con0
    wss
    wi
    #
    va
    wal
    wtru
    @8
    va
    vx
    cF
    va
    onsetrec.1
    onsetreclem2
    ax-gen
    a1i
    setrec2v
    trud
    @5
    va
    con0
    @3
    @2
    con0
    wcel
    #
    @4
    @3
    @7
    @0
    wss
    @9
    @2
    @7
    wcel
    @4
    @3
    @2
    @0
    cF
    @6
    @2
    cvv
    wcel
    @3
    va
    vex
    a1i
    @3
    id
    setrec1
    vx
    cF
    va
    onsetrec.1
    onsetreclem3
    @7
    @0
    @2
    ssel
    syl2im
    com12
    rgen
    va
    @0
    tfi
    mp2an
end
