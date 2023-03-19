include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "eliccxr.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "id.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "pnfge.mm"
include "syl.mm"
include "simpr.mm"
include "xrleneltd.mm"
include "elicod.mm"
include "sseldi.mm"

theorem ge0xrre
  let cA: class A


  assert |- ( ( A e. ( 0 [,] +oo ) /\ A =/= +oo ) -> A e. RR )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    wcel
    #
    cA
    cpnf
    wne
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    cr
    cA
    rge0ssre
    @2
    cc0
    cpnf
    cA
    cc0
    cxr
    wcel
    #
    @2
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    @2
    pnfxr
    a1i
    #
    @0
    cA
    cxr
    wcel
    #
    @1
    cA
    cc0
    cpnf
    eliccxr
    #
    adantr
    #
    @0
    cc0
    cA
    cle
    wbr
    #
    @1
    @0
    @3
    @4
    @0
    @9
    @3
    @0
    0xr
    a1i
    @4
    @0
    pnfxr
    a1i
    @0
    id
    cc0
    cpnf
    cA
    iccgelb
    syl3anc
    adantr
    @2
    cA
    cpnf
    @8
    @5
    @0
    cA
    cpnf
    cle
    wbr
    #
    @1
    @0
    @6
    @10
    @7
    cA
    pnfge
    syl
    adantr
    @0
    @1
    simpr
    xrleneltd
    elicod
    sseldi
end
