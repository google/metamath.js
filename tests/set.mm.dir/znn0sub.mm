include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cn0.mm"
include "wb.mm"
include "cr.mm"
include "zre.mm"
include "subge0.mm"
include "syl2an.mm"
include "zsubcl.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "ancoms.mm"
include "elnn0z.mm"
include "syl6bbr.mm"

theorem znn0sub
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M <_ N <-> ( N - M ) e. NN0 ) )

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
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cmin
    co
    #
    cz
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @3
    cn0
    wcel
    @1
    @0
    @2
    @6
    wb
    @1
    @0
    wa
    #
    @5
    @2
    @6
    @1
    cN
    cr
    wcel
    cM
    cr
    wcel
    @5
    @2
    wb
    @0
    cN
    zre
    cM
    zre
    cN
    cM
    subge0
    syl2an
    @7
    @4
    @5
    cN
    cM
    zsubcl
    biantrurd
    bitr3d
    ancoms
    @3
    elnn0z
    syl6bbr
end
