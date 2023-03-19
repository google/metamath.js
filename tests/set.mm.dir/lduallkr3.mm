include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "csca.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "eqid.mm"
include "lkrshp3.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "ldual0v.mm"
include "neeq2d.mm"
include "bitr4d.mm"

theorem lduallkr3
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume lduallkr3.h: |- H = ( LSHyp ` W )
  assume lduallkr3.f: |- F = ( LFnl ` W )
  assume lduallkr3.k: |- K = ( LKer ` W )
  assume lduallkr3.d: |- D = ( LDual ` W )
  assume lduallkr3.o: |- .0. = ( 0g ` D )
  assume lduallkr3.w: |- ( ph -> W e. LVec )
  assume lduallkr3.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( K ` G ) e. H <-> G =/= .0. ) )

  proof
    wph
    cG
    cK
    cfv
    cH
    wcel
    cG
    cW
    cbs
    cfv
    #
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
    wne
    cG
    c.0
    wne
    wph
    @1
    cF
    cG
    cH
    cK
    @0
    cW
    @2
    @0
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    lduallkr3.h
    lduallkr3.f
    lduallkr3.k
    lduallkr3.w
    lduallkr3.g
    lkrshp3
    wph
    c.0
    @3
    cG
    wph
    cD
    @1
    c.0
    @0
    cW
    @2
    @4
    @5
    @6
    lduallkr3.d
    lduallkr3.o
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    lduallkr3.w
    cW
    lveclmod
    syl
    ldual0v
    neeq2d
    bitr4d
end
