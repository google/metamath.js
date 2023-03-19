include "clss.mm"
include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "clspn.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "clmod.mm"
include "wb.mm"
include "eqid.mm"
include "islshp.mm"
include "syl.mm"
include "mpbid.mm"
include "simp2d.mm"

theorem lshpne
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cV: class V
  let cW: class W
  let vv: setvar v
  assume lshpne.v: |- V = ( Base ` W )
  assume lshpne.h: |- H = ( LSHyp ` W )
  assume lshpne.w: |- ( ph -> W e. LMod )
  assume lshpne.u: |- ( ph -> U e. H )


  assert |- ( ph -> U =/= V )

  proof
    wph
    cU
    cW
    clss
    cfv
    #
    wcel
    #
    cU
    cV
    wne
    #
    cU
    vv
    cv
    csn
    cun
    cW
    clspn
    cfv
    #
    cfv
    cV
    wceq
    vv
    cV
    wrex
    #
    wph
    cU
    cH
    wcel
    #
    @1
    @2
    @4
    w3a
    #
    lshpne.u
    wph
    cW
    clmod
    wcel
    @5
    @6
    wb
    lshpne.w
    vv
    @0
    cU
    cH
    @3
    cV
    cW
    clmod
    lshpne.v
    @3
    eqid
    @0
    eqid
    lshpne.h
    islshp
    syl
    mpbid
    simp2d
end
