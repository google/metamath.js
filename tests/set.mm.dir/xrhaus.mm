include "cle.mm"
include "ctsr.mm"
include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "cha.mm"
include "letsr.mm"
include "ordthaus.mm"
include "ax-mp.mm"

theorem xrhaus



  assert |- ( ordTop ` <_ ) e. Haus

  proof
    cle
    ctsr
    wcel
    cle
    cordt
    cfv
    cha
    wcel
    letsr
    cle
    ordthaus
    ax-mp
end
