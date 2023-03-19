include "cv.mm"
include "cuni.mm"
include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "wral.mm"
include "cfn.mm"
include "cdif.mm"
include "wb.mm"
include "vuniex.mm"
include "vpwex.mm"
include "pm3.2i.mm"
include "rgenw.mm"
include "pwinfig.mm"
include "ax-mp.mm"

theorem pwinfi
  let cA: class A
  let vx: setvar x


  assert |- ( A e. ( _V \ Fin ) <-> ~P A e. ( _V \ Fin ) )

  proof
    vx
    cv
    #
    cuni
    cvv
    wcel
    #
    @0
    cpw
    cvv
    wcel
    #
    wa
    #
    vx
    cvv
    wral
    cA
    cvv
    cfn
    cdif
    #
    wcel
    cA
    cpw
    @4
    wcel
    wb
    @3
    vx
    cvv
    @1
    @2
    vx
    vuniex
    vx
    vpwex
    pm3.2i
    rgenw
    vx
    cA
    cvv
    pwinfig
    ax-mp
end
