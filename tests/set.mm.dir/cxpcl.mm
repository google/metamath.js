include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cxpval.mm"
include "ax-1cn.mm"
include "0cn.mm"
include "keepel.mm"
include "a1i.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "id.mm"
include "logcl.mm"
include "mulcl.mm"
include "syl2anr.mm"
include "an32s.mm"
include "efcl.mm"
include "syl.mm"
include "sylan2br.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem cxpcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A ^c B ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    ccxp
    co
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cif
    cc
    cA
    cB
    cxpval
    @2
    @3
    @5
    @8
    cc
    @5
    cc
    wcel
    @2
    @3
    wa
    @4
    c1
    cc0
    cc
    ax-1cn
    0cn
    keepel
    a1i
    @3
    wn
    @2
    cA
    cc0
    wne
    #
    @8
    cc
    wcel
    #
    cA
    cc0
    df-ne
    @2
    @9
    wa
    @7
    cc
    wcel
    #
    @10
    @0
    @9
    @1
    @11
    @1
    @1
    @6
    cc
    wcel
    @11
    @0
    @9
    wa
    @1
    id
    cA
    logcl
    cB
    @6
    mulcl
    syl2anr
    an32s
    @7
    efcl
    syl
    sylan2br
    ifclda
    eqeltrd
end
