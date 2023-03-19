include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "eqid.mm"
include "qusval.mm"
include "quslem.mm"
include "imasbas.mm"

theorem qusbas
  let wph: wff ph
  let c.sm: class .~
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume qusbas.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusbas.v: |- ( ph -> V = ( Base ` R ) )
  assume qusbas.e: |- ( ph -> .~ e. W )
  assume qusbas.r: |- ( ph -> R e. Z )


  assert |- ( ph -> ( V /. .~ ) = ( Base ` U ) )

  proof
    wph
    cV
    c.sm
    cqs
    cR
    cU
    vx
    cV
    vx
    cv
    c.sm
    cec
    cmpt
    #
    cV
    cZ
    wph
    vx
    c.sm
    cR
    cU
    @0
    cV
    cW
    cZ
    qusbas.u
    qusbas.v
    @0
    eqid
    #
    qusbas.e
    qusbas.r
    qusval
    qusbas.v
    wph
    vx
    c.sm
    cR
    cU
    @0
    cV
    cW
    cZ
    qusbas.u
    qusbas.v
    @1
    qusbas.e
    qusbas.r
    quslem
    qusbas.r
    imasbas
end
