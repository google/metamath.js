include "cumgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "wf1.mm"
include "f10d.mm"
include "f1f.mm"
include "syl.mm"
include "wb.mm"
include "eqid.mm"
include "isumgr.mm"
include "mpbird.mm"

theorem umgr0e
  let wph: wff ph
  let cG: class G
  let cW: class W
  let vx: setvar x
  assume umgr0e.g: |- ( ph -> G e. W )
  assume umgr0e.e: |- ( ph -> ( iEdg ` G ) = (/) )


  assert |- ( ph -> G e. UMGraph )

  proof
    wph
    cG
    cumgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    crab
    #
    @1
    wf
    #
    wph
    @2
    @4
    @1
    wf1
    @5
    wph
    @4
    @1
    umgr0e.e
    f10d
    @2
    @4
    @1
    f1f
    syl
    wph
    cG
    cW
    wcel
    @0
    @5
    wb
    umgr0e.g
    vx
    cW
    @1
    cG
    @3
    @3
    eqid
    @1
    eqid
    isumgr
    syl
    mpbird
end
