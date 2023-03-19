include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqidd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "lsmelvalm.mm"
include "mpbird.mm"

theorem lsmelvalmi
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmelvalm.m: |- .- = ( -g ` G )
  assume lsmelvalm.p: |- .(+) = ( LSSum ` G )
  assume lsmelvalm.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmelvalm.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmelvalmi.x: |- ( ph -> X e. T )
  assume lsmelvalmi.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( X .- Y ) e. ( T .(+) U ) )

  proof
    wph
    cX
    cY
    c.mi
    co
    #
    cT
    cU
    c.po
    co
    wcel
    @0
    vx
    cv
    vy
    cv
    c.mi
    co
    wceq
    vy
    cU
    wrex
    vx
    cT
    wrex
    #
    wph
    cX
    cT
    wcel
    cY
    cU
    wcel
    @0
    @0
    wceq
    @1
    lsmelvalmi.x
    lsmelvalmi.y
    wph
    @0
    eqidd
    vx
    vy
    cT
    cU
    cX
    cY
    @0
    c.mi
    rspceov
    syl3anc
    wph
    vx
    vy
    c.po
    cT
    cU
    cG
    c.mi
    @0
    lsmelvalm.m
    lsmelvalm.p
    lsmelvalm.t
    lsmelvalm.u
    lsmelvalm
    mpbird
end
