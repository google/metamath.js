include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "evth2.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfral.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "cbvrexf.mm"
include "breq2d.mm"
include "cbvralf.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"

theorem evth2f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume evth2f.1: |- F/_ x F
  assume evth2f.2: |- F/_ y F
  assume evth2f.3: |- F/_ x X
  assume evth2f.4: |- F/_ y X
  assume evth2f.5: |- X = U. J
  assume evth2f.6: |- K = ( topGen ` ran (,) )
  assume evth2f.7: |- ( ph -> J e. Comp )
  assume evth2f.8: |- ( ph -> F e. ( J Cn K ) )
  assume evth2f.9: |- ( ph -> X =/= (/) )

  disjoint x y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint F a
  disjoint F b
  disjoint J a
  disjoint J b
  disjoint X a
  disjoint X b
  disjoint a ph
  disjoint b ph
  disjoint K b
  assert |- ( ph -> E. x e. X A. y e. X ( F ` x ) <_ ( F ` y ) )

  proof
    wph
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vb
    cX
    wral
    #
    va
    cX
    wrex
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cX
    wrex
    #
    wph
    va
    vb
    cF
    cJ
    cK
    cX
    evth2f.5
    evth2f.6
    evth2f.7
    evth2f.8
    evth2f.9
    evth2
    @6
    @8
    @3
    cle
    wbr
    #
    vb
    cX
    wral
    #
    vx
    cX
    wrex
    @13
    @5
    @15
    va
    vx
    cX
    va
    cX
    nfcv
    evth2f.3
    @4
    vx
    vb
    cX
    evth2f.3
    vx
    @1
    @3
    cle
    vx
    @0
    cF
    evth2f.1
    vx
    @0
    nfcv
    nffv
    vx
    cle
    nfcv
    vx
    @2
    cF
    evth2f.1
    vx
    @2
    nfcv
    nffv
    nfbr
    nfral
    @15
    va
    nfv
    va
    vx
    weq
    #
    @4
    @14
    vb
    cX
    @16
    @1
    @8
    @3
    cle
    @0
    @7
    cF
    fveq2
    breq1d
    ralbidv
    cbvrexf
    @15
    @12
    vx
    cX
    @14
    @11
    vb
    vy
    cX
    vb
    cX
    nfcv
    evth2f.4
    vy
    @8
    @3
    cle
    vy
    @7
    cF
    evth2f.2
    vy
    @7
    nfcv
    nffv
    vy
    cle
    nfcv
    vy
    @2
    cF
    evth2f.2
    vy
    @2
    nfcv
    nffv
    nfbr
    @11
    vb
    nfv
    vb
    vy
    weq
    @3
    @10
    @8
    cle
    @2
    @9
    cF
    fveq2
    breq2d
    cbvralf
    rexbii
    bitri
    sylib
end
