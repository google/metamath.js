include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "srabase.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "sraaddg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "eqtrd.mm"

theorem sralmod0
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume sralmod0.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume sralmod0.z: |- ( ph -> .0. = ( 0g ` W ) )
  assume sralmod0.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> .0. = ( 0g ` A ) )

  proof
    wph
    c.0
    cW
    c0g
    cfv
    cA
    c0g
    cfv
    sralmod0.z
    wph
    va
    vb
    cW
    cbs
    cfv
    #
    cW
    cA
    wph
    @0
    eqidd
    wph
    cA
    cS
    cW
    sralmod0.a
    sralmod0.s
    srabase
    wph
    va
    cv
    @0
    wcel
    vb
    cv
    @0
    wcel
    wa
    va
    vb
    cW
    cplusg
    cfv
    cA
    cplusg
    cfv
    wph
    cA
    cS
    cW
    sralmod0.a
    sralmod0.s
    sraaddg
    oveqdr
    grpidpropd
    eqtrd
end
