include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccl.mm"
include "ctsu.mm"
include "wss.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "ctps.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "topontop.mm"
include "syl.mm"
include "gsumcl.mm"
include "snssd.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "sscls.mm"
include "syl2anc.mm"
include "ovex.mm"
include "snss.mm"
include "sylibr.mm"
include "tsmsgsum.mm"
include "eleqtrrd.mm"

theorem tsmsid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vx: setvar x
  let cJ: class J
  assume tsmsid.b: |- B = ( Base ` G )
  assume tsmsid.z: |- .0. = ( 0g ` G )
  assume tsmsid.1: |- ( ph -> G e. CMnd )
  assume tsmsid.2: |- ( ph -> G e. TopSp )
  assume tsmsid.a: |- ( ph -> A e. V )
  assume tsmsid.f: |- ( ph -> F : A --> B )
  assume tsmsid.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. ( G tsums F ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    #
    @0
    csn
    #
    cG
    ctopn
    cfv
    #
    ccl
    cfv
    cfv
    #
    cG
    cF
    ctsu
    co
    wph
    @1
    @3
    wss
    #
    @0
    @3
    wcel
    wph
    @2
    ctop
    wcel
    #
    @1
    @2
    cuni
    #
    wss
    @4
    wph
    @2
    cB
    ctopon
    cfv
    wcel
    #
    @5
    wph
    cG
    ctps
    wcel
    @7
    tsmsid.2
    cB
    @2
    cG
    tsmsid.b
    @2
    eqid
    #
    istps
    sylib
    #
    cB
    @2
    topontop
    syl
    wph
    @1
    cB
    @6
    wph
    @0
    cB
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    tsmsid.b
    tsmsid.z
    tsmsid.1
    tsmsid.a
    tsmsid.f
    tsmsid.w
    gsumcl
    snssd
    wph
    @7
    cB
    @6
    wceq
    @9
    cB
    @2
    toponuni
    syl
    sseqtrd
    @1
    @2
    @6
    @6
    eqid
    sscls
    syl2anc
    @0
    @3
    cG
    cF
    cgsu
    ovex
    snss
    sylibr
    wph
    cA
    cB
    cF
    cG
    @2
    cV
    c.0
    tsmsid.b
    tsmsid.z
    tsmsid.1
    tsmsid.2
    tsmsid.a
    tsmsid.f
    tsmsid.w
    @8
    tsmsgsum
    eleqtrrd
end
