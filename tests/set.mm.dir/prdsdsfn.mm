include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt2.mm"
include "eqid.mm"
include "xrltso.mm"
include "supex.mm"
include "fnmpt2i.mm"
include "prdsds.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem prdsdsfn
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cH: class H
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume prdsbas.p: |- P = ( S Xs_ R )
  assume prdsbas.s: |- ( ph -> S e. V )
  assume prdsbas.r: |- ( ph -> R e. W )
  assume prdsbas.b: |- B = ( Base ` P )
  assume prdsbas.i: |- ( ph -> dom R = I )
  assume prdsds.l: |- D = ( dist ` P )


  assert |- ( ph -> D Fn ( B X. B ) )

  proof
    wph
    cD
    cB
    cB
    cxp
    #
    wfn
    vf
    vg
    cB
    cB
    vx
    cI
    vx
    cv
    #
    vf
    cv
    cfv
    @1
    vg
    cv
    cfv
    @1
    cR
    cfv
    cds
    cfv
    co
    cmpt
    crn
    cc0
    csn
    cun
    #
    cxr
    clt
    csup
    #
    cmpt2
    #
    @0
    wfn
    vf
    vg
    cB
    cB
    @3
    @4
    @4
    eqid
    cxr
    @2
    clt
    xrltso
    supex
    fnmpt2i
    wph
    @0
    cD
    @4
    wph
    vx
    cB
    cD
    cP
    cR
    cS
    vf
    vg
    cI
    cV
    cW
    prdsbas.p
    prdsbas.s
    prdsbas.r
    prdsbas.b
    prdsbas.i
    prdsds.l
    prdsds
    fneq1d
    mpbiri
end
