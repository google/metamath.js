include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "ccrd.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "wf1.mm"
include "wex.mm"
include "com.mm"
include "wral.mm"
include "ficardom.mm"
include "isinf.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcva.mm"
include "syl2anr.mm"
include "wf1o.mm"
include "simprr.mm"
include "ficardid.mm"
include "ad2antlr.mm"
include "entr.mm"
include "syl2anc.mm"
include "ensymd.mm"
include "bren.mm"
include "sylib.mm"
include "f1of1.mm"
include "adantl.mm"
include "simplrl.mm"
include "f1ss.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem isinffi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vc: setvar c
  let va: setvar a

  disjoint A f
  disjoint B f
  disjoint A c
  disjoint A a
  disjoint c f
  disjoint a c
  disjoint a f
  disjoint B c
  disjoint B a
  assert |- ( ( -. A e. Fin /\ B e. Fin ) -> E. f f : B -1-1-> A )

  proof
    cA
    cfn
    wcel
    wn
    #
    cB
    cfn
    wcel
    #
    wa
    #
    vc
    cv
    #
    cA
    wss
    #
    @3
    cB
    ccrd
    cfv
    #
    cen
    wbr
    #
    wa
    #
    cB
    cA
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    vc
    @1
    @5
    com
    wcel
    @4
    @3
    va
    cv
    #
    cen
    wbr
    #
    wa
    #
    vc
    wex
    #
    va
    com
    wral
    @7
    vc
    wex
    #
    @0
    cB
    ficardom
    vc
    cA
    va
    isinf
    @14
    @15
    va
    @5
    com
    @11
    @5
    wceq
    #
    @13
    @7
    vc
    @16
    @12
    @6
    @4
    @11
    @5
    @3
    cen
    breq2
    anbi2d
    exbidv
    rspcva
    syl2anr
    @2
    @7
    wa
    #
    cB
    @3
    @8
    wf1o
    #
    vf
    wex
    #
    @10
    @17
    cB
    @3
    cen
    wbr
    @19
    @17
    @3
    cB
    @17
    @6
    @5
    cB
    cen
    wbr
    #
    @3
    cB
    cen
    wbr
    @2
    @4
    @6
    simprr
    @1
    @20
    @0
    @7
    cB
    ficardid
    ad2antlr
    @3
    @5
    cB
    entr
    syl2anc
    ensymd
    cB
    @3
    vf
    bren
    sylib
    @17
    @18
    @9
    vf
    @17
    @18
    @9
    @17
    @18
    wa
    cB
    @3
    @8
    wf1
    #
    @4
    @9
    @18
    @21
    @17
    cB
    @3
    @8
    f1of1
    adantl
    @2
    @4
    @6
    @18
    simplrl
    cB
    @3
    cA
    @8
    f1ss
    syl2anc
    ex
    eximdv
    mpd
    exlimddv
end
