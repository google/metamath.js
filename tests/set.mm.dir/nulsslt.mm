include "csur.mm"
include "cpw.mm"
include "wcel.mm"
include "c0.mm"
include "cvv.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "csslt.mm"
include "elex.mm"
include "0ex.mm"
include "jctil.mm"
include "0ss.mm"
include "a1i.mm"
include "elpwi.mm"
include "ral0.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"

theorem nulsslt
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ~P No -> (/) <<s A )

  proof
    cA
    csur
    cpw
    #
    wcel
    #
    c0
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    c0
    csur
    wss
    #
    cA
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    vy
    cA
    wral
    #
    vx
    c0
    wral
    #
    w3a
    c0
    cA
    csslt
    wbr
    @1
    @3
    @2
    cA
    @0
    elex
    0ex
    jctil
    @1
    @4
    @5
    @7
    @4
    @1
    csur
    0ss
    a1i
    cA
    csur
    elpwi
    @7
    @1
    @6
    vx
    ral0
    a1i
    3jca
    vx
    vy
    c0
    cA
    brsslt
    sylanbrc
end
