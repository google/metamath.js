include "ctopn.mm"
include "cfv.mm"
include "cbs.mm"
include "ctopon.mm"
include "wcel.mm"
include "ctps.mm"
include "cqtop.mm"
include "co.mm"
include "eqid.mm"
include "imastopn.mm"
include "wfo.mm"
include "istps.mm"
include "sylib.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "qtoptopon.mm"
include "syl2anc.mm"
include "imasbas.mm"
include "eleqtrd.mm"
include "eqeltrd.mm"
include "sylibr.mm"

theorem imastps
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let vx: setvar x
  let cJ: class J
  assume imastps.u: |- ( ph -> U = ( F "s R ) )
  assume imastps.v: |- ( ph -> V = ( Base ` R ) )
  assume imastps.f: |- ( ph -> F : V -onto-> B )
  assume imastps.r: |- ( ph -> R e. TopSp )


  assert |- ( ph -> U e. TopSp )

  proof
    wph
    cU
    ctopn
    cfv
    #
    cU
    cbs
    cfv
    #
    ctopon
    cfv
    #
    wcel
    cU
    ctps
    wcel
    wph
    @0
    cR
    ctopn
    cfv
    #
    cF
    cqtop
    co
    #
    @2
    wph
    cB
    cR
    cU
    cF
    @3
    @0
    cV
    ctps
    imastps.u
    imastps.v
    imastps.f
    imastps.r
    @3
    eqid
    #
    @0
    eqid
    #
    imastopn
    wph
    @4
    cB
    ctopon
    cfv
    #
    @2
    wph
    @3
    cV
    ctopon
    cfv
    #
    wcel
    cV
    cB
    cF
    wfo
    @4
    @7
    wcel
    wph
    @3
    cR
    cbs
    cfv
    #
    ctopon
    cfv
    #
    @8
    wph
    cR
    ctps
    wcel
    @3
    @10
    wcel
    imastps.r
    @9
    @3
    cR
    @9
    eqid
    @5
    istps
    sylib
    wph
    cV
    @9
    ctopon
    imastps.v
    fveq2d
    eleqtrrd
    imastps.f
    cF
    @3
    cV
    cB
    qtoptopon
    syl2anc
    wph
    cB
    @1
    ctopon
    wph
    cB
    cR
    cU
    cF
    cV
    ctps
    imastps.u
    imastps.v
    imastps.f
    imastps.r
    imasbas
    fveq2d
    eleqtrd
    eqeltrd
    @1
    @0
    cU
    @1
    eqid
    @6
    istps
    sylibr
end
