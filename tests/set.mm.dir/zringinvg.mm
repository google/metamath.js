include "cz.mm"
include "wcel.mm"
include "zring.mm"
include "cminusg.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "zcn.mm"
include "negidd.mm"
include "cgrp.mm"
include "wb.mm"
include "zringgrp.mm"
include "a1i.mm"
include "id.mm"
include "znegcl.mm"
include "zringbas.mm"
include "zringplusg.mm"
include "zring0.mm"
include "eqid.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem zringinvg
  let cA: class A


  assert |- ( A e. ZZ -> -u A = ( ( invg ` ZZring ) ` A ) )

  proof
    cA
    cz
    wcel
    #
    cA
    zring
    cminusg
    cfv
    #
    cfv
    #
    cA
    cneg
    #
    @0
    @2
    @3
    wceq
    #
    cA
    @3
    caddc
    co
    cc0
    wceq
    #
    @0
    cA
    cA
    zcn
    negidd
    @0
    zring
    cgrp
    wcel
    #
    @0
    @3
    cz
    wcel
    @4
    @5
    wb
    @6
    @0
    zringgrp
    a1i
    @0
    id
    cA
    znegcl
    cz
    caddc
    zring
    @1
    cA
    @3
    cc0
    zringbas
    zringplusg
    zring0
    @1
    eqid
    grpinvid1
    syl3anc
    mpbird
    eqcomd
end
