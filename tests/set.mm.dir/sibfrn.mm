include "cdm.mm"
include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "crn.mm"
include "cfn.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cdif.mm"
include "wral.mm"
include "csitg.mm"
include "w3a.mm"
include "issibf.mm"
include "mpbid.mm"
include "simp2d.mm"

theorem sibfrn
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cA: class A
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vw: setvar w
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sibfmbl.1: |- ( ph -> F e. dom ( W sitg M ) )


  assert |- ( ph -> ran F e. Fin )

  proof
    wph
    cF
    cM
    cdm
    cS
    cmbfm
    co
    wcel
    #
    cF
    crn
    #
    cfn
    wcel
    #
    cF
    ccnv
    vx
    cv
    csn
    cima
    cM
    cfv
    cc0
    cpnf
    cico
    co
    wcel
    vx
    @1
    c.0
    csn
    cdif
    wral
    #
    wph
    cF
    cW
    cM
    csitg
    co
    cdm
    wcel
    @0
    @2
    @3
    w3a
    sibfmbl.1
    wph
    vx
    cB
    cS
    c.x
    cF
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    issibf
    mpbid
    simp2d
end
