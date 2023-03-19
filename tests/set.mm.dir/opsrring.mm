include "cmps.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "eqid.mm"
include "psrring.mm"
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
include "ringpropd.mm"
include "mpbid.mm"

theorem opsrring
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cI: class I
  let cO: class O
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume opsrring.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrring.i: |- ( ph -> I e. V )
  assume opsrring.r: |- ( ph -> R e. Ring )
  assume opsrring.t: |- ( ph -> T C_ ( I X. I ) )


  assert |- ( ph -> O e. Ring )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    crg
    wcel
    cO
    crg
    wcel
    wph
    cR
    @0
    cI
    cV
    @0
    eqid
    #
    opsrring.i
    opsrring.r
    psrring
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
    opsrring.o
    opsrring.t
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
    opsrring.o
    opsrring.t
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
    opsrring.o
    opsrring.t
    opsrmulr
    oveqdr
    ringpropd
    mpbid
end
