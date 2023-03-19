include "cfv.mm"
include "wne.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "lkrshpor.mm"
include "orcomd.mm"
include "neor.mm"
include "sylib.mm"
include "wa.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "lshpne.mm"
include "ex.mm"
include "impbid.mm"

theorem lkrshp4
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume lkrshp4.v: |- V = ( Base ` W )
  assume lkrshp4.h: |- H = ( LSHyp ` W )
  assume lkrshp4.f: |- F = ( LFnl ` W )
  assume lkrshp4.k: |- K = ( LKer ` W )
  assume lkrshp4.w: |- ( ph -> W e. LVec )
  assume lkrshp4.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( K ` G ) =/= V <-> ( K ` G ) e. H ) )

  proof
    wph
    cG
    cK
    cfv
    #
    cV
    wne
    #
    @0
    cH
    wcel
    #
    wph
    @0
    cV
    wceq
    #
    @2
    wo
    @1
    @2
    wi
    wph
    @2
    @3
    wph
    cF
    cG
    cH
    cK
    cV
    cW
    lkrshp4.v
    lkrshp4.h
    lkrshp4.f
    lkrshp4.k
    lkrshp4.w
    lkrshp4.g
    lkrshpor
    orcomd
    @2
    @0
    cV
    neor
    sylib
    wph
    @2
    @1
    wph
    @2
    wa
    @0
    cH
    cV
    cW
    lkrshp4.v
    lkrshp4.h
    wph
    cW
    clmod
    wcel
    #
    @2
    wph
    cW
    clvec
    wcel
    @4
    lkrshp4.w
    cW
    lveclmod
    syl
    adantr
    wph
    @2
    simpr
    lshpne
    ex
    impbid
end
