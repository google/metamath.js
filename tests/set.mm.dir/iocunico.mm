include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "csn.mm"
include "cun.mm"
include "cioc.mm"
include "cico.mm"
include "un23.mm"
include "unundir.mm"
include "uncom.mm"
include "uneq2i.mm"
include "3eqtrri.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "ioounsn.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "simprr.mm"
include "snunioo.mm"
include "uneq12d.mm"
include "ioojoin.mm"
include "3eqtr3a.mm"

theorem iocunico
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ ( A < B /\ B < C ) ) -> ( ( A (,] B ) u. ( B [,) C ) ) = ( A (,) C ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cB
    cC
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    cioo
    co
    #
    cB
    csn
    #
    cun
    #
    @9
    cB
    cC
    cioo
    co
    #
    cun
    #
    cun
    #
    @10
    @11
    cun
    #
    cA
    cB
    cioc
    co
    #
    cB
    cC
    cico
    co
    #
    cun
    cA
    cC
    cioo
    co
    @14
    @8
    @11
    cun
    @9
    cun
    @10
    @11
    @9
    cun
    #
    cun
    @13
    @8
    @9
    @11
    un23
    @8
    @11
    @9
    unundir
    @17
    @12
    @10
    @11
    @9
    uncom
    uneq2i
    3eqtrri
    @7
    @10
    @15
    @12
    @16
    @7
    @0
    @1
    @4
    @10
    @15
    wceq
    @0
    @1
    @2
    @6
    simpl1
    @0
    @1
    @2
    @6
    simpl2
    #
    @3
    @4
    @5
    simprl
    cA
    cB
    ioounsn
    syl3anc
    @7
    @1
    @2
    @5
    @12
    @16
    wceq
    @18
    @0
    @1
    @2
    @6
    simpl3
    @3
    @4
    @5
    simprr
    cB
    cC
    snunioo
    syl3anc
    uneq12d
    cA
    cB
    cC
    ioojoin
    3eqtr3a
end
