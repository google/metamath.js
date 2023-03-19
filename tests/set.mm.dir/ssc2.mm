include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wss.mm"
include "wral.mm"
include "cdm.mm"
include "cssc.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "eqidd.mm"
include "sscfn2.mm"
include "sscrel.mm"
include "brrelex2i.mm"
include "dmexg.mm"
include "4syl.mm"
include "isssc.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem ssc2
  let wph: wff ph
  let cS: class S
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ssc2.1: |- ( ph -> H Fn ( S X. S ) )
  assume ssc2.2: |- ( ph -> H C_cat J )
  assume ssc2.3: |- ( ph -> X e. S )
  assume ssc2.4: |- ( ph -> Y e. S )


  assert |- ( ph -> ( X H Y ) C_ ( X J Y ) )

  proof
    wph
    cX
    cS
    wcel
    cY
    cS
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @0
    @1
    cJ
    co
    #
    wss
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    cX
    cY
    cH
    co
    #
    cX
    cY
    cJ
    co
    #
    wss
    #
    ssc2.3
    ssc2.4
    wph
    cS
    cJ
    cdm
    #
    cdm
    #
    wss
    #
    @5
    wph
    cH
    cJ
    cssc
    wbr
    #
    @11
    @5
    wa
    ssc2.2
    wph
    vx
    vy
    cS
    @10
    cH
    cJ
    cvv
    ssc2.1
    wph
    @10
    cH
    cJ
    ssc2.2
    wph
    @10
    eqidd
    sscfn2
    wph
    @12
    cJ
    cvv
    wcel
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    ssc2.2
    cH
    cJ
    cssc
    sscrel
    brrelex2i
    cJ
    cvv
    dmexg
    @9
    cvv
    dmexg
    4syl
    isssc
    mpbid
    simprd
    @4
    @8
    cX
    @1
    cH
    co
    #
    cX
    @1
    cJ
    co
    #
    wss
    vx
    vy
    cX
    cY
    cS
    cS
    @0
    cX
    wceq
    @2
    @13
    @3
    @14
    @0
    cX
    @1
    cH
    oveq1
    @0
    cX
    @1
    cJ
    oveq1
    sseq12d
    @1
    cY
    wceq
    @13
    @6
    @14
    @7
    @1
    cY
    cX
    cH
    oveq2
    @1
    cY
    cX
    cJ
    oveq2
    sseq12d
    rspc2va
    syl21anc
end
