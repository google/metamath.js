include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cuni.mm"
include "cdif.mm"
include "cfv.mm"
include "cin.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "simpl.mm"
include "unveldomd.mm"
include "simpr.mm"
include "probdif.mm"
include "syl3anc.mm"
include "probtot.mm"
include "wss.mm"
include "elssuni.mm"
include "sseqin2.mm"
include "sylib.mm"
include "fveq2d.mm"
include "oveqan12d.mm"
include "eqtrd.mm"

theorem probdsb
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prob /\ A e. dom P ) -> ( P ` ( U. dom P \ A ) ) = ( 1 - ( P ` A ) ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    wa
    #
    @1
    cuni
    #
    cA
    cdif
    cP
    cfv
    #
    @4
    cP
    cfv
    #
    @4
    cA
    cin
    #
    cP
    cfv
    #
    cmin
    co
    #
    c1
    cA
    cP
    cfv
    #
    cmin
    co
    @3
    @0
    @4
    @1
    wcel
    @2
    @5
    @9
    wceq
    @0
    @2
    simpl
    #
    @3
    cP
    @11
    unveldomd
    @0
    @2
    simpr
    @4
    cA
    cP
    probdif
    syl3anc
    @0
    @2
    @6
    c1
    @8
    @10
    cmin
    cP
    probtot
    @2
    @7
    cA
    cP
    @2
    cA
    @4
    wss
    @7
    cA
    wceq
    cA
    @1
    elssuni
    cA
    @4
    sseqin2
    sylib
    fveq2d
    oveqan12d
    eqtrd
end
