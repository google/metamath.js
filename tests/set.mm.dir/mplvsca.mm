include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "mplvsca2.mm"
include "mplbasss.mm"
include "sseldi.mm"
include "psrvsca.mm"

theorem mplvsca
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  assume mplvsca.p: |- P = ( I mPoly R )
  assume mplvsca.n: |- .xb = ( .s ` P )
  assume mplvsca.k: |- K = ( Base ` R )
  assume mplvsca.b: |- B = ( Base ` P )
  assume mplvsca.m: |- .x. = ( .r ` R )
  assume mplvsca.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mplvsca.x: |- ( ph -> X e. K )
  assume mplvsca.f: |- ( ph -> F e. B )

  disjoint I h
  assert |- ( ph -> ( X .xb F ) = ( ( D X. { X } ) oF .x. F ) )

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
    c.xb
    c.x
    vh
    cF
    cI
    cK
    cX
    @0
    eqid
    #
    cP
    cR
    @0
    c.xb
    cI
    mplvsca.p
    @2
    mplvsca.n
    mplvsca2
    mplvsca.k
    @1
    eqid
    #
    mplvsca.m
    mplvsca.d
    mplvsca.x
    wph
    cB
    @1
    cF
    @1
    cP
    cR
    @0
    cB
    cI
    mplvsca.p
    @2
    mplvsca.b
    @3
    mplbasss
    mplvsca.f
    sseldi
    psrvsca
end
