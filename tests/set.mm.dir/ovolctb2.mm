include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cun.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "simpl.mm"
include "nnssre.mm"
include "unss.mm"
include "sylanblc.mm"
include "cen.mm"
include "com.mm"
include "nnenom.mm"
include "domentr.mm"
include "mpan2.mm"
include "adantl.mm"
include "endom.mm"
include "ax-mp.mm"
include "unctb.mm"
include "sylancl.mm"
include "ensymi.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "ssex.mm"
include "syl.mm"
include "ssun2.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "sbth.mm"
include "syl2anc.mm"
include "ovolctb.mm"
include "ssun1.mm"
include "ovolssnul.mm"
include "mp3an1.mm"

theorem ovolctb2
  let cA: class A


  assert |- ( ( A C_ RR /\ A ~<_ NN ) -> ( vol* ` A ) = 0 )

  proof
    cA
    cr
    wss
    #
    cA
    cn
    cdom
    wbr
    #
    wa
    #
    cA
    cn
    cun
    #
    cr
    wss
    #
    @3
    covol
    cfv
    cc0
    wceq
    #
    cA
    covol
    cfv
    cc0
    wceq
    #
    @2
    @0
    cn
    cr
    wss
    @4
    @0
    @1
    simpl
    nnssre
    cA
    cn
    cr
    unss
    sylanblc
    #
    @2
    @4
    @3
    cn
    cen
    wbr
    #
    @5
    @7
    @2
    @3
    cn
    cdom
    wbr
    #
    cn
    @3
    cdom
    wbr
    #
    @8
    @2
    @3
    com
    cdom
    wbr
    #
    com
    cn
    cen
    wbr
    @9
    @2
    cA
    com
    cdom
    wbr
    #
    cn
    com
    cdom
    wbr
    #
    @11
    @1
    @12
    @0
    @1
    cn
    com
    cen
    wbr
    #
    @12
    nnenom
    cA
    cn
    com
    domentr
    mpan2
    adantl
    @14
    @13
    nnenom
    cn
    com
    endom
    ax-mp
    cA
    cn
    unctb
    sylancl
    cn
    com
    nnenom
    ensymi
    @3
    com
    cn
    domentr
    sylancl
    @2
    @3
    cvv
    wcel
    #
    cn
    @3
    wss
    @10
    @2
    @4
    @15
    @7
    @3
    cr
    reex
    ssex
    syl
    cn
    cA
    ssun2
    cn
    @3
    cvv
    ssdomg
    mpisyl
    @3
    cn
    sbth
    syl2anc
    @3
    ovolctb
    syl2anc
    cA
    @3
    wss
    @4
    @5
    @6
    cA
    cn
    ssun1
    cA
    @3
    ovolssnul
    mp3an1
    syl2anc
end
