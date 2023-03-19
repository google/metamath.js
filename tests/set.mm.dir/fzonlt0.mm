include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cfzo.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "fzon.mm"
include "bitr3d.mm"

theorem fzonlt0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( -. M < N <-> ( M ..^ N ) = (/) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    cM
    cle
    wbr
    #
    cM
    cN
    clt
    wbr
    wn
    #
    cM
    cN
    cfzo
    co
    c0
    wceq
    @1
    cN
    cr
    wcel
    cM
    cr
    wcel
    @2
    @3
    wb
    @0
    cN
    zre
    cM
    zre
    cN
    cM
    lenlt
    syl2anr
    cM
    cN
    fzon
    bitr3d
end
