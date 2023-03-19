include "cfv.mm"
include "wceq.mm"
include "csca.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "clmod.mm"
include "wcel.mm"
include "wb.mm"
include "eqid.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "ldual0v.mm"
include "eqeq2d.mm"
include "bitr4d.mm"

theorem lkr0f2
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lkr0f2.v: |- V = ( Base ` W )
  assume lkr0f2.f: |- F = ( LFnl ` W )
  assume lkr0f2.k: |- K = ( LKer ` W )
  assume lkr0f2.d: |- D = ( LDual ` W )
  assume lkr0f2.o: |- .0. = ( 0g ` D )
  assume lkr0f2.w: |- ( ph -> W e. LMod )
  assume lkr0f2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( K ` G ) = V <-> G = .0. ) )

  proof
    wph
    cG
    cK
    cfv
    cV
    wceq
    #
    cG
    cV
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    cxp
    #
    wceq
    #
    cG
    c.0
    wceq
    wph
    cW
    clmod
    wcel
    cG
    cF
    wcel
    @0
    @4
    wb
    lkr0f2.w
    lkr0f2.g
    @1
    cF
    cG
    cK
    cV
    cW
    @2
    @1
    eqid
    #
    @2
    eqid
    #
    lkr0f2.v
    lkr0f2.f
    lkr0f2.k
    lkr0f
    syl2anc
    wph
    c.0
    @3
    cG
    wph
    cD
    @1
    c.0
    cV
    cW
    @2
    lkr0f2.v
    @5
    @6
    lkr0f2.d
    lkr0f2.o
    lkr0f2.w
    ldual0v
    eqeq2d
    bitr4d
end
