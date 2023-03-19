include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "com.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "pwexg.mm"
include "adantr.mm"
include "simpr.mm"
include "sspwb.mm"
include "sylib.mm"
include "mapss.mm"
include "syl2anc.mm"
include "isfin3ds.mm"
include "ibi.mm"
include "ssralv.mm"
include "sylc.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "syl.mm"
include "mpbird.mm"

theorem ssfin3ds
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x
  assume isfin3ds.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. b e. _om ( a ` suc b ) C_ ( a ` b ) -> |^| ran a e. ran a ) }

  disjoint a b
  disjoint a g
  disjoint A a
  disjoint b g
  disjoint A b
  disjoint A g
  disjoint B a
  disjoint B b
  disjoint B g
  disjoint a f
  disjoint a x
  disjoint b f
  disjoint b x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A x
  disjoint B f
  disjoint B x
  assert |- ( ( A e. F /\ B C_ A ) -> B e. F )

  proof
    cA
    cF
    wcel
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    cF
    wcel
    #
    vx
    cv
    #
    csuc
    vf
    cv
    #
    cfv
    @4
    @5
    cfv
    wss
    vx
    com
    wral
    @5
    crn
    #
    cint
    @6
    wcel
    wi
    #
    vf
    cB
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    @2
    @9
    cA
    cpw
    #
    com
    cmap
    co
    #
    wss
    #
    @7
    vf
    @12
    wral
    #
    @10
    @2
    @11
    cvv
    wcel
    #
    @8
    @11
    wss
    #
    @13
    @0
    @15
    @1
    cA
    cF
    pwexg
    adantr
    @2
    @1
    @16
    @0
    @1
    simpr
    cB
    cA
    sspwb
    sylib
    @8
    @11
    com
    cvv
    mapss
    syl2anc
    @0
    @14
    @1
    @0
    @14
    vx
    cA
    vf
    vg
    cF
    cF
    va
    vb
    isfin3ds.f
    isfin3ds
    ibi
    adantr
    @7
    vf
    @9
    @12
    ssralv
    sylc
    @2
    cB
    cvv
    wcel
    #
    @3
    @10
    wb
    @1
    @0
    @17
    cB
    cA
    cF
    ssexg
    ancoms
    vx
    cB
    vf
    vg
    cF
    cvv
    va
    vb
    isfin3ds.f
    isfin3ds
    syl
    mpbird
end
