include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wne.mm"
include "cpr.mm"
include "cdm.mm"
include "wss.mm"
include "w3a.mm"
include "cvv.mm"
include "wcel.mm"
include "cxp.mm"
include "wn.mm"
include "wa.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "simpl1.mm"
include "dmexg.mm"
include "adantl.mm"
include "prss.mm"
include "simpl.mm"
include "sylbir.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "simpr.mm"
include "simpl2.mm"
include "nehash2.mm"
include "fundmge2nop0.mm"
include "syl2anc.mm"
include "ex.mm"
include "prcnel.mm"
include "pm2.61d1.mm"

theorem fun2dmnop0
  let cA: class A
  let cB: class B
  let cG: class G
  assume fun2dmnop.a: |- A e. _V
  assume fun2dmnop.b: |- B e. _V


  assert |- ( ( Fun ( G \ { (/) } ) /\ A =/= B /\ { A , B } C_ dom G ) -> -. G e. ( _V X. _V ) )

  proof
    cG
    c0
    csn
    cdif
    wfun
    #
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    cG
    cdm
    #
    wss
    #
    w3a
    #
    cG
    cvv
    wcel
    #
    cG
    cvv
    cvv
    cxp
    #
    wcel
    wn
    #
    @4
    @5
    @7
    @4
    @5
    wa
    #
    @0
    c2
    @2
    chash
    cfv
    cle
    wbr
    @7
    @0
    @1
    @3
    @5
    simpl1
    @8
    cA
    cB
    @2
    cvv
    @5
    @2
    cvv
    wcel
    @4
    cG
    cvv
    dmexg
    adantl
    @4
    cA
    @2
    wcel
    #
    @5
    @3
    @0
    @9
    @1
    @3
    @9
    cB
    @2
    wcel
    #
    wa
    #
    @9
    cA
    cB
    @2
    fun2dmnop.a
    fun2dmnop.b
    prss
    #
    @9
    @10
    simpl
    sylbir
    3ad2ant3
    adantr
    @4
    @10
    @5
    @3
    @0
    @10
    @1
    @3
    @11
    @10
    @12
    @9
    @10
    simpr
    sylbir
    3ad2ant3
    adantr
    @0
    @1
    @3
    @5
    simpl2
    nehash2
    cG
    fundmge2nop0
    syl2anc
    ex
    cG
    @6
    prcnel
    pm2.61d1
end
