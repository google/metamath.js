include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "ctps.mm"
include "eqid.mm"
include "qusval.mm"
include "quslem.mm"
include "imastps.mm"

theorem qustps
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cE: class E
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume qustps.u: |- ( ph -> U = ( R /s E ) )
  assume qustps.v: |- ( ph -> V = ( Base ` R ) )
  assume qustps.e: |- ( ph -> E e. W )
  assume qustps.r: |- ( ph -> R e. TopSp )


  assert |- ( ph -> U e. TopSp )

  proof
    wph
    cV
    cE
    cqs
    cR
    cU
    vx
    cV
    vx
    cv
    cE
    cec
    cmpt
    #
    cV
    wph
    vx
    cE
    cR
    cU
    @0
    cV
    cW
    ctps
    qustps.u
    qustps.v
    @0
    eqid
    #
    qustps.e
    qustps.r
    qusval
    qustps.v
    wph
    vx
    cE
    cR
    cU
    @0
    cV
    cW
    ctps
    qustps.u
    qustps.v
    @1
    qustps.e
    qustps.r
    quslem
    qustps.r
    imastps
end
