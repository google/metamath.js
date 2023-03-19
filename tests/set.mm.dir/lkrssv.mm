include "cfv.mm"
include "clss.mm"
include "wcel.mm"
include "wss.mm"
include "clmod.mm"
include "eqid.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "lssss.mm"
include "syl.mm"

theorem lkrssv
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  assume lkrssv.v: |- V = ( Base ` W )
  assume lkrssv.f: |- F = ( LFnl ` W )
  assume lkrssv.k: |- K = ( LKer ` W )
  assume lkrssv.w: |- ( ph -> W e. LMod )
  assume lkrssv.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( K ` G ) C_ V )

  proof
    wph
    cG
    cK
    cfv
    #
    cW
    clss
    cfv
    #
    wcel
    #
    @0
    cV
    wss
    wph
    cW
    clmod
    wcel
    cG
    cF
    wcel
    @2
    lkrssv.w
    lkrssv.g
    @1
    cF
    cG
    cK
    cW
    lkrssv.f
    lkrssv.k
    @1
    eqid
    #
    lkrlss
    syl2anc
    @1
    @0
    cV
    cW
    lkrssv.v
    @3
    lssss
    syl
end
