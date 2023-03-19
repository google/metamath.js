include "wcel.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "mplelbas.mm"
include "simprbi.mm"
include "syl.mm"

theorem mplelsfi
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let c.0: class .0.
  assume mplrcl.p: |- P = ( I mPoly R )
  assume mplrcl.b: |- B = ( Base ` P )
  assume mplelsfi.z: |- .0. = ( 0g ` R )
  assume mplelsfi.f: |- ( ph -> F e. B )
  assume mplelsfi.r: |- ( ph -> R e. V )


  assert |- ( ph -> F finSupp .0. )

  proof
    wph
    cF
    cB
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    mplelsfi.f
    @0
    cF
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    wcel
    @1
    @3
    cP
    cR
    @2
    cB
    cI
    cF
    c.0
    mplrcl.p
    @2
    eqid
    @3
    eqid
    mplelsfi.z
    mplrcl.b
    mplelbas
    simprbi
    syl
end
