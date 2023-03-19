include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "cr.mm"
include "zre.mm"
include "suble0.mm"
include "syl2an.mm"
include "0z.mm"
include "zsubcl.mm"
include "fzon.mm"
include "sylancr.mm"
include "bitr3d.mm"
include "ancoms.mm"

theorem fzo0n
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( N <_ M <-> ( 0 ..^ ( N - M ) ) = (/) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cM
    cle
    wbr
    #
    cc0
    cN
    cM
    cmin
    co
    #
    cfzo
    co
    c0
    wceq
    #
    wb
    @0
    @1
    wa
    #
    @3
    cc0
    cle
    wbr
    #
    @2
    @4
    @0
    cN
    cr
    wcel
    cM
    cr
    wcel
    @6
    @2
    wb
    @1
    cN
    zre
    cM
    zre
    cN
    cM
    suble0
    syl2an
    @5
    cc0
    cz
    wcel
    @3
    cz
    wcel
    @6
    @4
    wb
    0z
    cN
    cM
    zsubcl
    cc0
    @3
    fzon
    sylancr
    bitr3d
    ancoms
end
