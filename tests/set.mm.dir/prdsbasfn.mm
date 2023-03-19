include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "cixp.mm"
include "wcel.mm"
include "wfn.mm"
include "prdsbas2.mm"
include "eleqtrd.mm"
include "ixpfn.mm"
include "syl.mm"

theorem prdsbasfn
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsbasmpt.s: |- ( ph -> S e. V )
  assume prdsbasmpt.i: |- ( ph -> I e. W )
  assume prdsbasmpt.r: |- ( ph -> R Fn I )
  assume prdsbasmpt.t: |- ( ph -> T e. B )


  assert |- ( ph -> T Fn I )

  proof
    wph
    cT
    vx
    cI
    vx
    cv
    cR
    cfv
    cbs
    cfv
    #
    cixp
    #
    wcel
    cT
    cI
    wfn
    wph
    cT
    cB
    @1
    prdsbasmpt.t
    wph
    vx
    cB
    cR
    cS
    cI
    cV
    cW
    cY
    prdsbasmpt.y
    prdsbasmpt.b
    prdsbasmpt.s
    prdsbasmpt.i
    prdsbasmpt.r
    prdsbas2
    eleqtrd
    vx
    cI
    @0
    cT
    ixpfn
    syl
end
