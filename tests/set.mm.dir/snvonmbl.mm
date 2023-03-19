include "csn.mm"
include "cv.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cixp.mm"
include "cvoln.mm"
include "cdm.mm"
include "rrxsnicc.mm"
include "eqcomd.mm"
include "eqid.mm"
include "cr.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "iccvonmbl.mm"
include "eqeltrd.mm"

theorem snvonmbl
  let wph: wff ph
  let cA: class A
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume snvonmbl.1: |- ( ph -> X e. Fin )
  assume snvonmbl.2: |- ( ph -> A e. ( RR ^m X ) )


  assert |- ( ph -> { A } e. dom ( voln ` X ) )

  proof
    wph
    cA
    csn
    #
    vk
    cX
    vk
    cv
    cA
    cfv
    #
    @1
    cicc
    co
    cixp
    #
    cX
    cvoln
    cfv
    cdm
    #
    wph
    @2
    @0
    wph
    cA
    vk
    cX
    snvonmbl.2
    rrxsnicc
    eqcomd
    wph
    cA
    cA
    @3
    vk
    cX
    snvonmbl.1
    @3
    eqid
    wph
    cA
    cr
    cX
    cmap
    co
    wcel
    cX
    cr
    cA
    wf
    snvonmbl.2
    cA
    cr
    cX
    elmapi
    syl
    #
    @4
    iccvonmbl
    eqeltrd
end
