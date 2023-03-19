include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "iunid.mm"
include "vonmea.mm"
include "eqid.mm"
include "dmmeasal.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "sselda.mm"
include "snvonmbl.mm"
include "saliuncl.mm"
include "syl5eqelr.mm"

theorem ctvonmbl
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume ctvonmbl.1: |- ( ph -> X e. Fin )
  assume ctvonmbl.2: |- ( ph -> A C_ ( RR ^m X ) )
  assume ctvonmbl.3: |- ( ph -> A ~<_ _om )


  assert |- ( ph -> A e. dom ( voln ` X ) )

  proof
    wph
    cA
    vx
    cA
    vx
    cv
    #
    csn
    #
    ciun
    cX
    cvoln
    cfv
    #
    cdm
    #
    vx
    cA
    iunid
    wph
    @3
    vx
    @1
    cA
    wph
    @3
    @2
    wph
    cX
    ctvonmbl.1
    vonmea
    @3
    eqid
    dmmeasal
    ctvonmbl.3
    wph
    @0
    cA
    wcel
    #
    wa
    @0
    cX
    wph
    cX
    cfn
    wcel
    @4
    ctvonmbl.1
    adantr
    wph
    cA
    cr
    cX
    cmap
    co
    @0
    ctvonmbl.2
    sselda
    snvonmbl
    saliuncl
    syl5eqelr
end
