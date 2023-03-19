include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "ldual0v.mm"
include "clmod.mm"
include "wcel.mm"
include "lfl0f.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem ldual0vcl
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cW: class W
  let c.0: class .0.
  assume ldualv0cl.f: |- F = ( LFnl ` W )
  assume ldualv0cl.d: |- D = ( LDual ` W )
  assume ldualv0cl.o: |- .0. = ( 0g ` D )
  assume ldualv0cl.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> .0. e. F )

  proof
    wph
    c.0
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
    cF
    wph
    cD
    @1
    c.0
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
    ldualv0cl.d
    ldualv0cl.o
    ldualv0cl.w
    ldual0v
    wph
    cW
    clmod
    wcel
    @3
    cF
    wcel
    ldualv0cl.w
    @1
    cF
    @0
    cW
    @2
    @5
    @6
    @4
    ldualv0cl.f
    lfl0f
    syl
    eqeltrd
end
