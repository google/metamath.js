include "com.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "mpan.mm"
include "sspwb.mm"
include "sylib.mm"
include "sselda.mm"
include "nnfi.mm"
include "elpwi.mm"
include "ssfi.mm"
include "syl2an.mm"
include "elind.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ackbij2lem1
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H
  let cB: class B


  assert |- ( A e. _om -> ~P A C_ ( ~P _om i^i Fin ) )

  proof
    cA
    com
    wcel
    #
    va
    cA
    cpw
    #
    com
    cpw
    #
    cfn
    cin
    #
    @0
    va
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    @0
    @5
    wa
    @2
    cfn
    @4
    @0
    @1
    @2
    @4
    @0
    cA
    com
    wss
    #
    @1
    @2
    wss
    com
    word
    @0
    @6
    ordom
    com
    cA
    ordelss
    mpan
    cA
    com
    sspwb
    sylib
    sselda
    @0
    cA
    cfn
    wcel
    @4
    cA
    wss
    @4
    cfn
    wcel
    @5
    cA
    nnfi
    @4
    cA
    elpwi
    cA
    @4
    ssfi
    syl2an
    elind
    ex
    ssrdv
end
