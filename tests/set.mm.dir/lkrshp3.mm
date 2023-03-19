include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "wa.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "lshpne.mm"
include "wceq.mm"
include "wb.mm"
include "lkr0f.mm"
include "syl2anc.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "lkrshp.mm"
include "syl3anc.mm"
include "impbida.mm"

theorem lkrshp3
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lkrshp3.v: |- V = ( Base ` W )
  assume lkrshp3.d: |- D = ( Scalar ` W )
  assume lkrshp3.o: |- .0. = ( 0g ` D )
  assume lkrshp3.h: |- H = ( LSHyp ` W )
  assume lkrshp3.f: |- F = ( LFnl ` W )
  assume lkrshp3.k: |- K = ( LKer ` W )
  assume lkrshp3.w: |- ( ph -> W e. LVec )
  assume lkrshp3.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( K ` G ) e. H <-> G =/= ( V X. { .0. } ) ) )

  proof
    wph
    cG
    cK
    cfv
    #
    cH
    wcel
    #
    cG
    cV
    c.0
    csn
    cxp
    #
    wne
    #
    wph
    @1
    wa
    #
    @0
    cV
    wne
    @3
    @4
    @0
    cH
    cV
    cW
    lkrshp3.v
    lkrshp3.h
    wph
    cW
    clmod
    wcel
    #
    @1
    wph
    cW
    clvec
    wcel
    #
    @5
    lkrshp3.w
    cW
    lveclmod
    syl
    #
    adantr
    wph
    @1
    simpr
    lshpne
    @4
    @0
    cV
    cG
    @2
    wph
    @0
    cV
    wceq
    cG
    @2
    wceq
    wb
    #
    @1
    wph
    @5
    cG
    cF
    wcel
    #
    @8
    @7
    lkrshp3.g
    cD
    cF
    cG
    cK
    cV
    cW
    c.0
    lkrshp3.d
    lkrshp3.o
    lkrshp3.v
    lkrshp3.f
    lkrshp3.k
    lkr0f
    syl2anc
    adantr
    necon3bid
    mpbid
    wph
    @3
    wa
    @6
    @9
    @3
    @1
    wph
    @6
    @3
    lkrshp3.w
    adantr
    wph
    @9
    @3
    lkrshp3.g
    adantr
    wph
    @3
    simpr
    cD
    cF
    cG
    cH
    cK
    cV
    cW
    c.0
    lkrshp3.v
    lkrshp3.d
    lkrshp3.o
    lkrshp3.h
    lkrshp3.f
    lkrshp3.k
    lkrshp
    syl3anc
    impbida
end
