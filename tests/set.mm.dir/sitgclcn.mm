include "csca.mm"
include "cfv.mm"
include "ccnfld.mm"
include "crrext.mm"
include "cnrrext.mm"
include "syl6eqel.mm"
include "sitgclbn.mm"

theorem sitgclcn
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
  assume sitgclcn.1: |- ( ph -> W e. Ban )
  assume sitgclcn.2: |- ( ph -> ( Scalar ` W ) = CCfld )


  assert |- ( ph -> ( ( W sitg M ) ` F ) e. B )

  proof
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
    sitgclcn.1
    wph
    cW
    csca
    cfv
    ccnfld
    crrext
    sitgclcn.2
    cnrrext
    syl6eqel
    sitgclbn
end
