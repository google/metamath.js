include "com.mm"
include "cina.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "ctsk.mm"
include "omina.mm"
include "inatsk.mm"
include "ax-mp.mm"

theorem r1omtsk



  assert |- ( R1 ` _om ) e. Tarski

  proof
    com
    cina
    wcel
    com
    cr1
    cfv
    ctsk
    wcel
    omina
    com
    inatsk
    ax-mp
end
