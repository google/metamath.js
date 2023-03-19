include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "zsubcl.mm"
include "ancoms.mm"
include "dvdsadd.mm"
include "syldan.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan3.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem dvdssubr
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || ( N - M ) ) )

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
    #
    cM
    cN
    cM
    cmin
    co
    #
    cdvds
    wbr
    #
    cM
    cM
    @3
    caddc
    co
    #
    cdvds
    wbr
    #
    cM
    cN
    cdvds
    wbr
    @0
    @1
    @3
    cz
    wcel
    #
    @4
    @6
    wb
    @1
    @0
    @7
    cN
    cM
    zsubcl
    ancoms
    cM
    @3
    dvdsadd
    syldan
    @2
    @5
    cN
    cM
    cdvds
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @5
    cN
    wceq
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    pncan3
    syl2an
    breq2d
    bitr2d
end
