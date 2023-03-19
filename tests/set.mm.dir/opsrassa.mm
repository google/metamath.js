include "cmps.mm"
include "co.mm"
include "casa.mm"
include "wcel.mm"
include "eqid.mm"
include "psrassa.mm"
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
include "ccrg.mm"
include "psrsca.mm"
include "opsrsca.mm"
include "cvsca.mm"
include "opsrvsca.mm"
include "assapropd.mm"
include "mpbid.mm"

theorem opsrassa
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


  assert |- ( ph -> O e. AssAlg )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    casa
    wcel
    cO
    casa
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
    psrassa
    wph
    vx
    vy
    @0
    cbs
    cfv
    #
    cR
    cbs
    cfv
    #
    cR
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
    #
    @2
    wcel
    vy
    cv
    @2
    wcel
    #
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
    @6
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
    wph
    cR
    @0
    cI
    cV
    ccrg
    @1
    opsrcrng.i
    opsrcrng.r
    psrsca
    wph
    cR
    @0
    cT
    cI
    cO
    cV
    ccrg
    @1
    opsrcrng.o
    opsrcrng.t
    opsrcrng.i
    opsrcrng.r
    opsrsca
    @3
    eqid
    wph
    @4
    @3
    wcel
    @5
    wa
    vx
    vy
    @0
    cvsca
    cfv
    cO
    cvsca
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
    opsrvsca
    oveqdr
    assapropd
    mpbid
end
