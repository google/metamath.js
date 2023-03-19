include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "clss.mm"
include "cfv.mm"
include "wss.mm"
include "clspn.mm"
include "simpl.mm"
include "cbs.mm"
include "pweqi.mm"
include "eleq2i.mm"
include "lincolss.mm"
include "sylan2b.mm"
include "lcoss.mm"
include "eqid.mm"
include "lspssp.mm"
include "syl3anc.mm"

theorem lspsslco
  let cB: class B
  let cM: class M
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume lspeqvlco.b: |- B = ( Base ` M )


  assert |- ( ( M e. LMod /\ V e. ~P B ) -> ( ( LSpan ` M ) ` V ) C_ ( M LinCo V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    wa
    @0
    cM
    cV
    clinco
    co
    #
    cM
    clss
    cfv
    #
    wcel
    #
    cV
    @3
    wss
    #
    cV
    cM
    clspn
    cfv
    #
    cfv
    @3
    wss
    @0
    @2
    simpl
    @2
    @0
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    @5
    @1
    @9
    cV
    cB
    @8
    lspeqvlco.b
    pweqi
    eleq2i
    #
    cM
    cV
    lincolss
    sylan2b
    @2
    @0
    @10
    @6
    @11
    cM
    cV
    lcoss
    sylan2b
    @4
    cV
    @3
    @7
    cM
    @4
    eqid
    @7
    eqid
    lspssp
    syl3anc
end
