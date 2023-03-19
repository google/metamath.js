include "ldualvbase.mm"
include "eleqtrrd.mm"

theorem ldualelvbase
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  assume ldualelvbase.f: |- F = ( LFnl ` W )
  assume ldualelvbase.d: |- D = ( LDual ` W )
  assume ldualelvbase.v: |- V = ( Base ` D )
  assume ldualelvbase.w: |- ( ph -> W e. X )
  assume ldualelvbase.g: |- ( ph -> G e. F )


  assert |- ( ph -> G e. V )

  proof
    wph
    cG
    cF
    cV
    ldualelvbase.g
    wph
    cD
    cF
    cV
    cW
    cX
    ldualelvbase.f
    ldualelvbase.d
    ldualelvbase.v
    ldualelvbase.w
    ldualvbase
    eleqtrrd
end
