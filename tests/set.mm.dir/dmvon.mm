include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "covoln.mm"
include "ccaragen.mm"
include "cres.mm"
include "vonval.mm"
include "dmeqd.mm"
include "wss.mm"
include "wceq.mm"
include "come.mm"
include "wcel.mm"
include "ovnome.mm"
include "eqid.mm"
include "caragenss.mm"
include "syl.mm"
include "ssdmres.mm"
include "sylib.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem dmvon
  let wph: wff ph
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dmvon.x: |- ( ph -> X e. Fin )


  assert |- ( ph -> dom ( voln ` X ) = ( CaraGen ` ( voln* ` X ) ) )

  proof
    wph
    cX
    cvoln
    cfv
    #
    cdm
    cX
    covoln
    cfv
    #
    @1
    ccaragen
    cfv
    #
    cres
    #
    cdm
    #
    @2
    @2
    wph
    @0
    @3
    wph
    cX
    dmvon.x
    vonval
    dmeqd
    wph
    @2
    @1
    cdm
    wss
    #
    @4
    @2
    wceq
    wph
    @1
    come
    wcel
    @5
    wph
    cX
    dmvon.x
    ovnome
    @2
    @1
    @2
    eqid
    caragenss
    syl
    @2
    @1
    ssdmres
    sylib
    wph
    @2
    eqidd
    3eqtrd
end
