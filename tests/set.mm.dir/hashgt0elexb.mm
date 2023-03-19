include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "hashgt0elex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "hashgt0.mm"
include "sylan2br.mm"
include "impbida.mm"

theorem hashgt0elexb
  let vx: setvar x
  let cV: class V
  let cW: class W

  disjoint V x
  assert |- ( V e. W -> ( 0 < ( # ` V ) <-> E. x x e. V ) )

  proof
    cV
    cW
    wcel
    #
    cc0
    cV
    chash
    cfv
    clt
    wbr
    #
    vx
    cv
    cV
    wcel
    vx
    wex
    #
    vx
    cV
    cW
    hashgt0elex
    @2
    @0
    cV
    c0
    wne
    @1
    vx
    cV
    n0
    cV
    cW
    hashgt0
    sylan2br
    impbida
end
