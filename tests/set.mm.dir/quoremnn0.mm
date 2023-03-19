include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "fldivnn0.mm"
include "syl5eqel.mm"
include "nn0z.mm"
include "quoremz.mm"
include "sylan.mm"
include "simpl.mm"
include "anim1i.mm"
include "anasss.mm"
include "syl2anc.mm"

theorem quoremnn0
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume quorem.1: |- Q = ( |_ ` ( A / B ) )
  assume quorem.2: |- R = ( A - ( B x. Q ) )


  assert |- ( ( A e. NN0 /\ B e. NN ) -> ( ( Q e. NN0 /\ R e. NN0 ) /\ ( R < B /\ A = ( ( B x. Q ) + R ) ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cQ
    cn0
    wcel
    #
    cQ
    cz
    wcel
    #
    cR
    cn0
    wcel
    #
    wa
    #
    cR
    cB
    clt
    wbr
    cA
    cB
    cQ
    cmul
    co
    cR
    caddc
    co
    wceq
    wa
    #
    wa
    #
    @3
    @5
    wa
    #
    @7
    wa
    #
    @2
    cQ
    cA
    cB
    cdiv
    co
    cfl
    cfv
    cn0
    quorem.1
    cA
    cB
    fldivnn0
    syl5eqel
    @0
    cA
    cz
    wcel
    @1
    @8
    cA
    nn0z
    cA
    cB
    cQ
    cR
    quorem.1
    quorem.2
    quoremz
    sylan
    @3
    @6
    @7
    @10
    @3
    @6
    wa
    @9
    @7
    @3
    @4
    @5
    @9
    @3
    @4
    wa
    @3
    @5
    @3
    @4
    simpl
    anim1i
    anasss
    anim1i
    anasss
    syl2anc
end
