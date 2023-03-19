include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "mplbasss.mm"
include "sseldi.mm"
include "psrelbas.mm"

theorem mplelf
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cI: class I
  let cK: class K
  let cX: class X
  assume mplelf.p: |- P = ( I mPoly R )
  assume mplelf.k: |- K = ( Base ` R )
  assume mplelf.b: |- B = ( Base ` P )
  assume mplelf.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplelf.x: |- ( ph -> X e. B )

  disjoint I f
  assert |- ( ph -> X : D --> K )

  proof
    wph
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    cD
    cR
    @0
    vf
    cI
    cK
    cX
    @0
    eqid
    #
    mplelf.k
    mplelf.d
    @1
    eqid
    #
    wph
    cB
    @1
    cX
    @1
    cP
    cR
    @0
    cB
    cI
    mplelf.p
    @2
    mplelf.b
    @3
    mplbasss
    mplelf.x
    sseldi
    psrelbas
end
