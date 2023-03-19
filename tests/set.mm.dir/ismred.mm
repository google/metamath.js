include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "cmre.mm"
include "cfv.mm"
include "selpw.mm"
include "3expia.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "ismre.mm"
include "syl3anbrc.mm"

theorem ismred
  let wph: wff ph
  let cC: class C
  let cX: class X
  let vs: setvar s
  assume ismred.ss: |- ( ph -> C C_ ~P X )
  assume ismred.ba: |- ( ph -> X e. C )
  assume ismred.in: |- ( ( ph /\ s C_ C /\ s =/= (/) ) -> |^| s e. C )

  disjoint ph s
  disjoint C s
  disjoint X s
  assert |- ( ph -> C e. ( Moore ` X ) )

  proof
    wph
    cC
    cX
    cpw
    wss
    cX
    cC
    wcel
    vs
    cv
    #
    c0
    wne
    #
    @0
    cint
    cC
    wcel
    #
    wi
    #
    vs
    cC
    cpw
    #
    wral
    cC
    cX
    cmre
    cfv
    wcel
    ismred.ss
    ismred.ba
    wph
    @3
    vs
    @4
    @0
    @4
    wcel
    wph
    @0
    cC
    wss
    #
    @3
    vs
    cC
    selpw
    wph
    @5
    @1
    @2
    ismred.in
    3expia
    sylan2b
    ralrimiva
    cC
    cX
    vs
    ismre
    syl3anbrc
end
