include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elxnn0.mm"
include "2a1.mm"
include "wa.mm"
include "wb.mm"
include "breq1.mm"
include "adantr.mm"
include "cxr.mm"
include "nn0re.mm"
include "rexrd.mm"
include "xgepnf.mm"
include "syl.mm"
include "cr.mm"
include "wnel.mm"
include "pnfnre.mm"
include "eleq1.mm"
include "elnelall.mm"
include "syl6bi.mm"
include "com13.mm"
include "ax-mp.mm"
include "sylbid.mm"
include "adantl.mm"
include "ex.mm"
include "jaoi.mm"
include "sylbi.mm"
include "3imp.mm"

theorem xnn0lenn0nn0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0* /\ N e. NN0 /\ M <_ N ) -> M e. NN0 )

  proof
    cM
    cxnn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    cM
    cn0
    wcel
    #
    @0
    @3
    cM
    cpnf
    wceq
    #
    wo
    @1
    @2
    @3
    wi
    #
    wi
    #
    cM
    elxnn0
    @3
    @6
    @4
    @3
    @1
    @2
    2a1
    @4
    @1
    @5
    @4
    @1
    wa
    @2
    cpnf
    cN
    cle
    wbr
    #
    @3
    @4
    @2
    @7
    wb
    @1
    cM
    cpnf
    cN
    cle
    breq1
    adantr
    @1
    @7
    @3
    wi
    @4
    @1
    @7
    cN
    cpnf
    wceq
    #
    @3
    @1
    cN
    cxr
    wcel
    @7
    @8
    wb
    @1
    cN
    cN
    nn0re
    rexrd
    cN
    xgepnf
    syl
    cpnf
    cr
    wnel
    #
    @1
    @8
    @3
    wi
    wi
    pnfnre
    @8
    @1
    @9
    @3
    @8
    @1
    cpnf
    cn0
    wcel
    #
    @9
    @3
    wi
    #
    cN
    cpnf
    cn0
    eleq1
    @10
    cpnf
    cr
    wcel
    @11
    cpnf
    nn0re
    @3
    cpnf
    cr
    elnelall
    syl
    syl6bi
    com13
    ax-mp
    sylbid
    adantl
    sylbid
    ex
    jaoi
    sylbi
    3imp
end
