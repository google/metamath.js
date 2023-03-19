include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfn.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "simpr.mm"
include "simplr.mm"
include "hashnncl.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "nnge1d.mm"
include "wn.mm"
include "cpnf.mm"
include "cxr.mm"
include "1re.mm"
include "rexri.mm"
include "pnfge.mm"
include "ax-mp.mm"
include "wceq.mm"
include "hashinf.mm"
include "adantlr.mm"
include "syl5breqr.mm"
include "pm2.61dan.mm"

theorem hashge1
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ A =/= (/) ) -> 1 <_ ( # ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cfn
    wcel
    #
    c1
    cA
    chash
    cfv
    #
    cle
    wbr
    @2
    @3
    wa
    #
    @4
    @5
    @3
    @1
    @4
    cn
    wcel
    #
    @2
    @3
    simpr
    @0
    @1
    @3
    simplr
    @3
    @6
    @1
    cA
    hashnncl
    biimpar
    syl2anc
    nnge1d
    @2
    @3
    wn
    #
    wa
    c1
    cpnf
    @4
    cle
    c1
    cxr
    wcel
    c1
    cpnf
    cle
    wbr
    c1
    1re
    rexri
    c1
    pnfge
    ax-mp
    @0
    @7
    @4
    cpnf
    wceq
    @1
    cA
    cV
    hashinf
    adantlr
    syl5breqr
    pm2.61dan
end
