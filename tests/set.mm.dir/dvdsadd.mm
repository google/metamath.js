include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmin.mm"
include "wb.mm"
include "simpl.mm"
include "zaddcl.mm"
include "simpr.mm"
include "iddvds.mm"
include "adantr.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan.mm"
include "syl2an.mm"
include "breqtrrd.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "bicomd.mm"

theorem dvdsadd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || ( M + N ) ) )

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
    cM
    cN
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
    #
    @2
    @0
    @3
    cz
    wcel
    @1
    cM
    @3
    cN
    cmin
    co
    #
    cdvds
    wbr
    @4
    @5
    wb
    @0
    @1
    simpl
    cM
    cN
    zaddcl
    @0
    @1
    simpr
    @2
    cM
    cM
    @6
    cdvds
    @0
    cM
    cM
    cdvds
    wbr
    @1
    cM
    iddvds
    adantr
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @6
    cM
    wceq
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    pncan
    syl2an
    breqtrrd
    cM
    @3
    cN
    dvdssub2
    syl31anc
    bicomd
end
