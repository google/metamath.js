include "csur.mm"
include "cpw.mm"
include "wcel.mm"
include "cvv.mm"
include "c0.mm"
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
include "jctir.mm"
include "elpwi.mm"
include "0ss.mm"
include "a1i.mm"
include "ral0.mm"
include "rgenw.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"

theorem nulssgt
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ~P No -> A <<s (/) )

  proof
    cA
    csur
    cpw
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    c0
    cvv
    wcel
    #
    wa
    cA
    csur
    wss
    #
    c0
    csur
    wss
    #
    vx
    cv
    vy
    cv
    cslt
    wbr
    #
    vy
    c0
    wral
    #
    vx
    cA
    wral
    #
    w3a
    cA
    c0
    csslt
    wbr
    @1
    @2
    @3
    cA
    @0
    elex
    0ex
    jctir
    @1
    @4
    @5
    @8
    cA
    csur
    elpwi
    @5
    @1
    csur
    0ss
    a1i
    @8
    @1
    @7
    vx
    cA
    @6
    vy
    ral0
    rgenw
    a1i
    3jca
    vx
    vy
    cA
    c0
    brsslt
    sylanbrc
end
