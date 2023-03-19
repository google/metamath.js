include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "p0val.mm"
include "syl.mm"
include "glble.mm"
include "eqbrtrd.mm"

theorem p0le
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume p0le.b: |- B = ( Base ` K )
  assume p0le.g: |- G = ( glb ` K )
  assume p0le.l: |- .<_ = ( le ` K )
  assume p0le.0: |- .0. = ( 0. ` K )
  assume p0le.k: |- ( ph -> K e. V )
  assume p0le.x: |- ( ph -> X e. B )
  assume p0le.d: |- ( ph -> B e. dom G )


  assert |- ( ph -> .0. .<_ X )

  proof
    wph
    c.0
    cB
    cG
    cfv
    #
    cX
    c.le
    wph
    cK
    cV
    wcel
    c.0
    @0
    wceq
    p0le.k
    cB
    cG
    cK
    cV
    c.0
    p0le.b
    p0le.g
    p0le.0
    p0val
    syl
    wph
    cB
    cB
    cG
    cK
    c.le
    cV
    cX
    p0le.b
    p0le.l
    p0le.g
    p0le.k
    p0le.d
    p0le.x
    glble
    eqbrtrd
end
