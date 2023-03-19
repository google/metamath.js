include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "dvdsnegb.mm"
include "wb.mm"
include "znegcl.mm"
include "dvdsadd.mm"
include "sylan2.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "breq2d.mm"
include "3bitrd.mm"

theorem dvdssub
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || ( M - N ) ) )

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
    cdvds
    wbr
    cM
    cN
    cneg
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
    cM
    cN
    cmin
    co
    #
    cdvds
    wbr
    cM
    cN
    dvdsnegb
    @1
    @0
    @3
    cz
    wcel
    @4
    @6
    wb
    cN
    znegcl
    cM
    @3
    dvdsadd
    sylan2
    @2
    @5
    @7
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
    @7
    wceq
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    negsub
    syl2an
    breq2d
    3bitrd
end
