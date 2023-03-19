include "csubgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wss.mm"
include "ciedg.mm"
include "cedg.mm"
include "cpw.mm"
include "ssid.mm"
include "syl5sseq.mm"
include "cres.mm"
include "resss.mm"
include "syl6eqss.mm"
include "uhgrspansubgrlem.mm"
include "cuhgr.mm"
include "wcel.mm"
include "wfun.mm"
include "w3a.mm"
include "wb.mm"
include "uhgrfun.mm"
include "syl.mm"
include "eqid.mm"
include "issubgr2.mm"
include "syl3anc.mm"
include "mpbir3and.mm"

theorem uhgrspansubgr
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vi: setvar i
  assume uhgrspan.v: |- V = ( Vtx ` G )
  assume uhgrspan.e: |- E = ( iEdg ` G )
  assume uhgrspan.s: |- ( ph -> S e. W )
  assume uhgrspan.q: |- ( ph -> ( Vtx ` S ) = V )
  assume uhgrspan.r: |- ( ph -> ( iEdg ` S ) = ( E |` A ) )
  assume uhgrspan.g: |- ( ph -> G e. UHGraph )


  assert |- ( ph -> S SubGraph G )

  proof
    wph
    cS
    cG
    csubgr
    wbr
    #
    cS
    cvtx
    cfv
    #
    cV
    wss
    #
    cS
    ciedg
    cfv
    #
    cE
    wss
    #
    cS
    cedg
    cfv
    #
    @1
    cpw
    wss
    #
    wph
    @1
    @1
    cV
    @1
    ssid
    uhgrspan.q
    syl5sseq
    wph
    @3
    cE
    cA
    cres
    cE
    uhgrspan.r
    cE
    cA
    resss
    syl6eqss
    wph
    cA
    cS
    cE
    cG
    cV
    cW
    uhgrspan.v
    uhgrspan.e
    uhgrspan.s
    uhgrspan.q
    uhgrspan.r
    uhgrspan.g
    uhgrspansubgrlem
    wph
    cG
    cuhgr
    wcel
    #
    cE
    wfun
    #
    cS
    cW
    wcel
    @0
    @2
    @4
    @6
    w3a
    wb
    uhgrspan.g
    wph
    @7
    @8
    uhgrspan.g
    cE
    cG
    uhgrspan.e
    uhgrfun
    syl
    uhgrspan.s
    cV
    cE
    cS
    cW
    @5
    cG
    @3
    @1
    cuhgr
    @1
    eqid
    uhgrspan.v
    @3
    eqid
    uhgrspan.e
    @5
    eqid
    issubgr2
    syl3anc
    mpbir3and
end
