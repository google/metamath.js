include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "eqid.mm"
include "mdegmullem.mm"

theorem mdegmulle2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegmulle2.b: |- B = ( Base ` Y )
  assume mdegmulle2.t: |- .x. = ( .r ` Y )
  assume mdegmulle2.f: |- ( ph -> F e. B )
  assume mdegmulle2.g: |- ( ph -> G e. B )
  assume mdegmulle2.j1: |- ( ph -> J e. NN0 )
  assume mdegmulle2.k1: |- ( ph -> K e. NN0 )
  assume mdegmulle2.j2: |- ( ph -> ( D ` F ) <_ J )
  assume mdegmulle2.k2: |- ( ph -> ( D ` G ) <_ K )


  assert |- ( ph -> ( D ` ( F .x. G ) ) <_ ( J + K ) )

  proof
    wph
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    cB
    cD
    cR
    c.x
    cF
    cG
    vb
    @0
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    cI
    cJ
    cK
    cV
    cY
    va
    vb
    mdegaddle.y
    mdegaddle.d
    mdegaddle.i
    mdegaddle.r
    mdegmulle2.b
    mdegmulle2.t
    mdegmulle2.f
    mdegmulle2.g
    mdegmulle2.j1
    mdegmulle2.k1
    mdegmulle2.j2
    mdegmulle2.k2
    @0
    eqid
    @1
    eqid
    mdegmullem
end
