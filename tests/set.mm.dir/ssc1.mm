include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cssc.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "sscrel.mm"
include "brrelex2i.mm"
include "syl.mm"
include "ssclem.mm"
include "mpbid.mm"
include "isssc.mm"
include "simpld.mm"

theorem ssc1
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isssc.1: |- ( ph -> H Fn ( S X. S ) )
  assume isssc.2: |- ( ph -> J Fn ( T X. T ) )
  assume ssc1.3: |- ( ph -> H C_cat J )


  assert |- ( ph -> S C_ T )

  proof
    wph
    cS
    cT
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    @1
    @2
    cJ
    co
    wss
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wph
    cH
    cJ
    cssc
    wbr
    #
    @0
    @3
    wa
    ssc1.3
    wph
    vx
    vy
    cS
    cT
    cH
    cJ
    cvv
    isssc.1
    isssc.2
    wph
    cJ
    cvv
    wcel
    #
    cT
    cvv
    wcel
    wph
    @4
    @5
    ssc1.3
    cH
    cJ
    cssc
    sscrel
    brrelex2i
    syl
    wph
    cT
    cJ
    isssc.2
    ssclem
    mpbid
    isssc
    mpbid
    simpld
end
