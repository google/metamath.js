include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "come.mm"
include "wcel.mm"
include "wb.mm"
include "isome.mm"
include "syl.mm"
include "mpbid.mm"
include "simplld.mm"
include "simprd.mm"

theorem ome0
  let wph: wff ph
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume ome0.1: |- ( ph -> O e. OutMeas )


  assert |- ( ph -> ( O ` (/) ) = 0 )

  proof
    wph
    cO
    cdm
    #
    cc0
    cpnf
    cicc
    co
    cO
    wf
    @0
    @0
    cuni
    cpw
    #
    wceq
    wa
    #
    c0
    cO
    cfv
    cc0
    wceq
    #
    wph
    @2
    @3
    wa
    #
    vy
    cv
    cO
    cfv
    vx
    cv
    #
    cO
    cfv
    cle
    wbr
    vy
    @5
    cpw
    wral
    vx
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    @5
    cuni
    cO
    cfv
    cO
    @5
    cres
    csumge0
    cfv
    cle
    wbr
    wi
    vx
    @0
    cpw
    wral
    #
    wph
    cO
    come
    wcel
    #
    @4
    @6
    wa
    @7
    wa
    #
    ome0.1
    wph
    @8
    @8
    @9
    wb
    ome0.1
    vx
    vy
    cO
    come
    isome
    syl
    mpbid
    simplld
    simprd
end
