include "cmps.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "eqid.mm"
include "psrlmod.mm"
include "cbs.mm"
include "cfv.mm"
include "eqidd.mm"
include "opsrbas.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "opsrplusg.mm"
include "oveqdr.mm"
include "crg.mm"
include "psrsca.mm"
include "opsrsca.mm"
include "cvsca.mm"
include "opsrvsca.mm"
include "lmodpropd.mm"
include "mpbid.mm"

theorem opsrlmod
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


  assert |- ( ph -> O e. LMod )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    clmod
    wcel
    cO
    clmod
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
    psrlmod
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
    opsrring.o
    opsrring.t
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
    cR
    @0
    cI
    cV
    crg
    @1
    opsrring.i
    opsrring.r
    psrsca
    wph
    cR
    @0
    cT
    cI
    cO
    cV
    crg
    @1
    opsrring.o
    opsrring.t
    opsrring.i
    opsrring.r
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
    opsrring.o
    opsrring.t
    opsrvsca
    oveqdr
    lmodpropd
    mpbid
end
