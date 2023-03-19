include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "evth.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvralf.mm"
include "rexbii.mm"
include "nfral.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "cbvrexf.mm"
include "bitri.mm"
include "sylib.mm"

theorem evthf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume evthf.1: |- F/_ x F
  assume evthf.2: |- F/_ y F
  assume evthf.3: |- F/_ x X
  assume evthf.4: |- F/_ y X
  assume evthf.5: |- F/ x ph
  assume evthf.6: |- F/ y ph
  assume evthf.7: |- X = U. J
  assume evthf.8: |- K = ( topGen ` ran (,) )
  assume evthf.9: |- ( ph -> J e. Comp )
  assume evthf.10: |- ( ph -> F e. ( J Cn K ) )
  assume evthf.11: |- ( ph -> X =/= (/) )

  disjoint x y
  disjoint a b
  disjoint a y
  disjoint b y
  disjoint a x
  disjoint F a
  disjoint F b
  disjoint J a
  disjoint J b
  disjoint X a
  disjoint X b
  disjoint a ph
  disjoint b ph
  disjoint K b
  assert |- ( ph -> E. x e. X A. y e. X ( F ` y ) <_ ( F ` x ) )

  proof
    wph
    vb
    cv
    #
    cF
    cfv
    #
    va
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
    vy
    cv
    #
    cF
    cfv
    #
    vx
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
    evthf.7
    evthf.8
    evthf.9
    evthf.10
    evthf.11
    evth
    @6
    @8
    @3
    cle
    wbr
    #
    vy
    cX
    wral
    #
    va
    cX
    wrex
    @13
    @5
    @15
    va
    cX
    @4
    @14
    vb
    vy
    cX
    vb
    cX
    nfcv
    evthf.4
    vy
    @1
    @3
    cle
    vy
    @0
    cF
    evthf.2
    vy
    @0
    nfcv
    nffv
    vy
    cle
    nfcv
    vy
    @2
    cF
    evthf.2
    vy
    @2
    nfcv
    nffv
    nfbr
    @14
    vb
    nfv
    vb
    vy
    weq
    @1
    @8
    @3
    cle
    @0
    @7
    cF
    fveq2
    breq1d
    cbvralf
    rexbii
    @15
    @12
    va
    vx
    cX
    va
    cX
    nfcv
    evthf.3
    @14
    vx
    vy
    cX
    evthf.3
    vx
    @8
    @3
    cle
    vx
    @7
    cF
    evthf.1
    vx
    @7
    nfcv
    nffv
    vx
    cle
    nfcv
    vx
    @2
    cF
    evthf.1
    vx
    @2
    nfcv
    nffv
    nfbr
    nfral
    @12
    va
    nfv
    va
    vx
    weq
    #
    @14
    @11
    vy
    cX
    @16
    @3
    @10
    @8
    cle
    @2
    @9
    cF
    fveq2
    breq2d
    ralbidv
    cbvrexf
    bitri
    sylib
end
