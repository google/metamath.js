include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
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
include "simp1d.mm"

theorem lshplss
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cW: class W
  let vv: setvar v
  assume lshplss.s: |- S = ( LSubSp ` W )
  assume lshplss.h: |- H = ( LSHyp ` W )
  assume lshplss.w: |- ( ph -> W e. LMod )
  assume lshplss.u: |- ( ph -> U e. H )


  assert |- ( ph -> U e. S )

  proof
    wph
    cU
    cS
    wcel
    #
    cU
    cW
    cbs
    cfv
    #
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
    @1
    wceq
    vv
    @1
    wrex
    #
    wph
    cU
    cH
    wcel
    #
    @0
    @2
    @4
    w3a
    #
    lshplss.u
    wph
    cW
    clmod
    wcel
    @5
    @6
    wb
    lshplss.w
    vv
    cS
    cU
    cH
    @3
    @1
    cW
    clmod
    @1
    eqid
    @3
    eqid
    lshplss.s
    lshplss.h
    islshp
    syl
    mpbid
    simp1d
end
