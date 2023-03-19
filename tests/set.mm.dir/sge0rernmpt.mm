include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "clt.mm"
include "cmpt.mm"
include "crn.mm"
include "wn.mm"
include "wceq.mm"
include "simpr.mm"
include "wb.mm"
include "nltpnft.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "eqid.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "fmptdf.mm"
include "sge0rern.mm"
include "ad2antrr.mm"
include "condan.mm"
include "elicod.mm"

theorem sge0rernmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vk: setvar k
  assume sge0rernmpt.xph: |- F/ x ph
  assume sge0rernmpt.a: |- ( ph -> A e. V )
  assume sge0rernmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0rernmpt.re: |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. RR )

  disjoint A x
  disjoint k x
  assert |- ( ( ph /\ x e. A ) -> B e. ( 0 [,) +oo ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cc0
    cpnf
    cB
    cc0
    cxr
    wcel
    #
    @1
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @1
    pnfxr
    a1i
    #
    @1
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cB
    cc0
    cpnf
    iccssxr
    sge0rernmpt.b
    sseldi
    #
    @1
    @2
    @4
    cB
    @6
    wcel
    #
    cc0
    cB
    cle
    wbr
    @3
    @5
    sge0rernmpt.b
    cc0
    cpnf
    cB
    iccgelb
    syl3anc
    @1
    cB
    cpnf
    clt
    wbr
    #
    cpnf
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    wcel
    #
    @1
    @9
    wn
    #
    wa
    #
    cpnf
    cB
    @11
    @14
    cB
    cpnf
    @14
    cB
    cpnf
    wceq
    #
    @13
    @1
    @13
    simpr
    @1
    @15
    @13
    wb
    #
    @13
    @1
    cB
    cxr
    wcel
    @16
    @7
    cB
    nltpnft
    syl
    adantr
    mpbird
    eqcomd
    @1
    cB
    @11
    wcel
    #
    @13
    @1
    @0
    @8
    @17
    wph
    @0
    simpr
    sge0rernmpt.b
    vx
    cA
    cB
    @10
    @6
    @10
    eqid
    #
    elrnmpt1
    syl2anc
    adantr
    eqeltrd
    wph
    @12
    wn
    @0
    @13
    wph
    @10
    cV
    cA
    sge0rernmpt.a
    wph
    vx
    cA
    cB
    @6
    @10
    sge0rernmpt.xph
    sge0rernmpt.b
    @18
    fmptdf
    sge0rernmpt.re
    sge0rern
    ad2antrr
    condan
    elicod
end
