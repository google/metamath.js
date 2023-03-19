include "cc.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "restsspw.mm"
include "sseldi.mm"
include "elpwi.mm"
include "syl.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "sstrd.mm"

theorem dvdmsscn
  let wph: wff ph
  let cS: class S
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dvdmsscn.s: |- ( ph -> S e. { RR , CC } )
  assume dvdmsscn.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )


  assert |- ( ph -> X C_ CC )

  proof
    wph
    cX
    cS
    cc
    wph
    cX
    cS
    cpw
    #
    wcel
    cX
    cS
    wss
    wph
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    @0
    cX
    cS
    @1
    restsspw
    dvdmsscn.x
    sseldi
    cX
    cS
    elpwi
    syl
    wph
    cS
    cr
    cc
    cpr
    wcel
    cS
    cc
    wss
    dvdmsscn.s
    cS
    recnprss
    syl
    sstrd
end
