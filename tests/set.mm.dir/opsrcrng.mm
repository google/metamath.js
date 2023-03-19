include "cmps.mm"
include "co.mm"
include "ccrg.mm"
include "wcel.mm"
include "eqid.mm"
include "psrcrng.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "opsrbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "opsrplusg.mm"
include "oveqdr.mm"
include "cmulr.mm"
include "opsrmulr.mm"
include "crngpropd.mm"
include "mpbid.mm"

theorem opsrcrng
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cI: class I
  let cO: class O
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume opsrcrng.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrcrng.i: |- ( ph -> I e. V )
  assume opsrcrng.r: |- ( ph -> R e. CRing )
  assume opsrcrng.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> O e. CRing )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    ccrg
    wcel
    cO
    ccrg
    wcel
    wph
    cR
    @0
    cI
    cV
    @0
    eqid
    #
    opsrcrng.i
    opsrcrng.r
    psrcrng
    wph
    vx
    vy
    @0
    cbs
    cfv
    #
    @0
    cO
    wph
    @2
    eqidd
    wph
    cR
    @0
    cT
    cI
    cO
    @1
    opsrcrng.o
    opsrcrng.t
    opsrbas
    wph
    vx
    cv
    @2
    wcel
    vy
    cv
    @2
    wcel
    wa
    #
    vx
    vy
    @0
    cplusg
    cfv
    cO
    cplusg
    cfv
    wph
    cR
    @0
    cT
    cI
    cO
    @1
    opsrcrng.o
    opsrcrng.t
    opsrplusg
    oveqdr
    wph
    @3
    vx
    vy
    @0
    cmulr
    cfv
    cO
    cmulr
    cfv
    wph
    cR
    @0
    cT
    cI
    cO
    @1
    opsrcrng.o
    opsrcrng.t
    opsrmulr
    oveqdr
    crngpropd
    mpbid
end
