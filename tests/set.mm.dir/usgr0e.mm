include "cusgr.mm"
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
include "wf1.mm"
include "f10d.mm"
include "wb.mm"
include "eqid.mm"
include "isusgr.mm"
include "syl.mm"
include "mpbird.mm"

theorem usgr0e
  let wph: wff ph
  let cG: class G
  let cW: class W
  let vx: setvar x
  assume usgr0e.g: |- ( ph -> G e. W )
  assume usgr0e.e: |- ( ph -> ( iEdg ` G ) = (/) )


  assert |- ( ph -> G e. USGraph )

  proof
    wph
    cG
    cusgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    cdm
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
    wf1
    #
    wph
    @3
    @1
    usgr0e.e
    f10d
    wph
    cG
    cW
    wcel
    @0
    @4
    wb
    usgr0e.g
    vx
    cW
    @1
    cG
    @2
    @2
    eqid
    @1
    eqid
    isusgr
    syl
    mpbird
end
