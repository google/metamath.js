include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "csca.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "wa.mm"
include "clmod.mm"
include "wb.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "olcd.mm"
include "wne.mm"
include "adantr.mm"
include "simpr.mm"
include "lkrshp.mm"
include "syl3anc.mm"
include "orcd.mm"
include "pm2.61dane.mm"

theorem lkrshpor
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume lkrshpor.v: |- V = ( Base ` W )
  assume lkrshpor.h: |- H = ( LSHyp ` W )
  assume lkrshpor.f: |- F = ( LFnl ` W )
  assume lkrshpor.k: |- K = ( LKer ` W )
  assume lkrshpor.w: |- ( ph -> W e. LVec )
  assume lkrshpor.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( K ` G ) e. H \/ ( K ` G ) = V ) )

  proof
    wph
    cG
    cK
    cfv
    #
    cH
    wcel
    #
    @0
    cV
    wceq
    #
    wo
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
    wph
    cG
    @5
    wceq
    #
    wa
    @2
    @1
    wph
    @2
    @6
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    @2
    @6
    wb
    wph
    cW
    clvec
    wcel
    #
    @7
    lkrshpor.w
    cW
    lveclmod
    syl
    lkrshpor.g
    @3
    cF
    cG
    cK
    cV
    cW
    @4
    @3
    eqid
    #
    @4
    eqid
    #
    lkrshpor.v
    lkrshpor.f
    lkrshpor.k
    lkr0f
    syl2anc
    biimpar
    olcd
    wph
    cG
    @5
    wne
    #
    wa
    #
    @1
    @2
    @13
    @9
    @8
    @12
    @1
    wph
    @9
    @12
    lkrshpor.w
    adantr
    wph
    @8
    @12
    lkrshpor.g
    adantr
    wph
    @12
    simpr
    @3
    cF
    cG
    cH
    cK
    cV
    cW
    @4
    lkrshpor.v
    @10
    @11
    lkrshpor.h
    lkrshpor.f
    lkrshpor.k
    lkrshp
    syl3anc
    orcd
    pm2.61dane
end
