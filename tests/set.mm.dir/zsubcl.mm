include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "znegcl.mm"
include "zaddcl.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem zsubcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M - N ) e. ZZ )

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
    cneg
    #
    caddc
    co
    #
    cM
    cN
    cmin
    co
    #
    cz
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @3
    @4
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
    @1
    @0
    @2
    cz
    wcel
    @3
    cz
    wcel
    cN
    znegcl
    cM
    @2
    zaddcl
    sylan2
    eqeltrrd
end
