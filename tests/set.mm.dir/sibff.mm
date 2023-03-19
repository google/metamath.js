include "cdm.mm"
include "cuni.mm"
include "wf.mm"
include "cmeas.mm"
include "crn.mm"
include "wcel.mm"
include "csiga.mm"
include "dmmeas.mm"
include "syl.mm"
include "csigagen.mm"
include "cfv.mm"
include "cvv.mm"
include "ctopn.mm"
include "fvexd.mm"
include "syl5eqel.mm"
include "sgsiga.mm"
include "sibfmbl.mm"
include "mbfmf.mm"
include "unieqi.mm"
include "wceq.mm"
include "unisg.mm"
include "syl5eq.mm"
include "feq3d.mm"
include "mpbid.mm"

theorem sibff
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


  assert |- ( ph -> F : U. dom M --> U. J )

  proof
    wph
    cM
    cdm
    #
    cuni
    #
    cS
    cuni
    #
    cF
    wf
    @1
    cJ
    cuni
    #
    cF
    wf
    wph
    @0
    cS
    cF
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    @0
    csiga
    crn
    cuni
    #
    wcel
    sitgval.2
    cM
    dmmeas
    syl
    wph
    cS
    cJ
    csigagen
    cfv
    #
    @4
    sitgval.s
    wph
    cJ
    cvv
    wph
    cJ
    cW
    ctopn
    cfv
    cvv
    sitgval.j
    wph
    cW
    ctopn
    fvexd
    syl5eqel
    #
    sgsiga
    syl5eqel
    wph
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
    sibfmbl.1
    sibfmbl
    mbfmf
    wph
    @2
    @3
    cF
    @1
    wph
    @2
    @5
    cuni
    #
    @3
    cS
    @5
    sitgval.s
    unieqi
    wph
    cJ
    cvv
    wcel
    @7
    @3
    wceq
    @6
    cJ
    cvv
    unisg
    syl
    syl5eq
    feq3d
    mpbid
end
