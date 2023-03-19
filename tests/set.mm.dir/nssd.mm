include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "jca.mm"
include "wceq.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "nss.mm"
include "sylibr.mm"

theorem nssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x
  assume nssd.1: |- ( ph -> X e. A )
  assume nssd.2: |- ( ph -> -. X e. B )


  assert |- ( ph -> -. A C_ B )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    cA
    cB
    wss
    wn
    wph
    cX
    cA
    wcel
    #
    @6
    cX
    cB
    wcel
    #
    wn
    #
    wa
    #
    @5
    nssd.1
    wph
    @6
    @8
    nssd.1
    nssd.2
    jca
    @4
    @9
    vx
    cX
    cA
    @0
    cX
    wceq
    #
    @1
    @6
    @3
    @8
    @0
    cX
    cA
    eleq1
    @10
    @2
    @7
    @0
    cX
    cB
    eleq1
    notbid
    anbi12d
    spcegv
    sylc
    vx
    cA
    cB
    nss
    sylibr
end
