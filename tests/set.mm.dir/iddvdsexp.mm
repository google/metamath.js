include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "zexpcl.mm"
include "sylan2.mm"
include "simpl.mm"
include "dvdsmul2.mm"
include "syl2anc.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "expm1t.mm"
include "sylan.mm"
include "breqtrrd.mm"

theorem iddvdsexp
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN ) -> M || ( M ^ N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cM
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cM
    cmul
    co
    #
    cM
    cN
    cexp
    co
    #
    cdvds
    @2
    @4
    cz
    wcel
    #
    @0
    cM
    @5
    cdvds
    wbr
    @1
    @0
    @3
    cn0
    wcel
    @7
    cN
    nnm1nn0
    cM
    @3
    zexpcl
    sylan2
    @0
    @1
    simpl
    @4
    cM
    dvdsmul2
    syl2anc
    @0
    cM
    cc
    wcel
    @1
    @6
    @5
    wceq
    cM
    zcn
    cM
    cN
    expm1t
    sylan
    breqtrrd
end
