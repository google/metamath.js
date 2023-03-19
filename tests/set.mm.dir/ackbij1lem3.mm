include "com.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "mpan.mm"
include "elpwg.mm"
include "mpbird.mm"
include "nnfi.mm"
include "elind.mm"

theorem ackbij1lem3
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


  assert |- ( A e. _om -> A e. ( ~P _om i^i Fin ) )

  proof
    cA
    com
    wcel
    #
    com
    cpw
    #
    cfn
    cA
    @0
    cA
    @1
    wcel
    cA
    com
    wss
    #
    com
    word
    @0
    @2
    ordom
    com
    cA
    ordelss
    mpan
    cA
    com
    com
    elpwg
    mpbird
    cA
    nnfi
    elind
end
