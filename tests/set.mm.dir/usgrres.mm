include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "c0.mm"
include "crn.mm"
include "wss.mm"
include "usgrf.mm"
include "wnel.mm"
include "ssrab3.mm"
include "a1i.mm"
include "f1ssres.mm"
include "syl2an2r.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "umgrreslem.mm"
include "sylan.mm"
include "f1ssr.mm"
include "syl2anc.mm"
include "wb.mm"
include "ssdmres.mm"
include "mpbi.mm"
include "f1eq2.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "cvv.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "cvtx.mm"
include "uhgrspan1lem2.mm"
include "eqcomi.mm"
include "ciedg.mm"
include "uhgrspan1lem3.mm"
include "isusgrs.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem usgrres
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vj: setvar j
  let vp: setvar p
  let vx: setvar x
  assume upgrres.v: |- V = ( Vtx ` G )
  assume upgrres.e: |- E = ( iEdg ` G )
  assume upgrres.f: |- F = { i e. dom E | N e/ ( E ` i ) }
  assume upgrres.s: |- S = <. ( V \ { N } ) , ( E |` F ) >.

  disjoint E i
  disjoint N i
  disjoint E j
  disjoint i j
  disjoint E p
  disjoint j p
  disjoint F j
  disjoint G j
  disjoint G p
  disjoint N j
  disjoint N p
  disjoint V j
  disjoint V p
  disjoint S p
  disjoint G x
  disjoint V x
  assert |- ( ( G e. USGraph /\ N e. V ) -> S e. USGraph )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cS
    cusgr
    wcel
    #
    cE
    cF
    cres
    #
    cdm
    #
    vp
    cv
    chash
    cfv
    c2
    wceq
    vp
    cV
    cN
    csn
    cdif
    #
    cpw
    crab
    #
    @4
    wf1
    #
    @2
    cF
    @7
    @4
    wf1
    #
    @8
    @2
    cF
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    c0
    csn
    cdif
    crab
    #
    @4
    wf1
    #
    @4
    crn
    @7
    wss
    #
    @9
    @0
    cE
    cdm
    #
    @10
    cE
    wf1
    @1
    cF
    @13
    wss
    #
    @11
    vx
    cE
    cG
    cV
    upgrres.v
    upgrres.e
    usgrf
    @14
    @2
    cN
    vi
    cv
    cE
    cfv
    wnel
    vi
    @13
    cF
    upgrres.f
    ssrab3
    #
    a1i
    @13
    @10
    cF
    cE
    f1ssres
    syl2an2r
    @0
    cG
    cumgr
    wcel
    @1
    @12
    cG
    usgrumgr
    vi
    cE
    cF
    cG
    cN
    cV
    vp
    upgrres.v
    upgrres.e
    upgrres.f
    umgrreslem
    sylan
    cF
    @10
    @7
    @4
    f1ssr
    syl2anc
    @5
    cF
    wceq
    #
    @8
    @9
    wb
    @14
    @16
    @15
    cF
    cE
    ssdmres
    mpbi
    @5
    cF
    @7
    @4
    f1eq2
    ax-mp
    sylibr
    cS
    cvv
    wcel
    @3
    @8
    wb
    @2
    cS
    @6
    @4
    cop
    cvv
    upgrres.s
    @6
    @4
    opex
    eqeltri
    vp
    cvv
    @4
    cS
    @6
    cS
    cvtx
    cfv
    @6
    cS
    vi
    cF
    cG
    cE
    cN
    cV
    upgrres.v
    upgrres.e
    upgrres.f
    upgrres.s
    uhgrspan1lem2
    eqcomi
    cS
    ciedg
    cfv
    @4
    cS
    vi
    cF
    cG
    cE
    cN
    cV
    upgrres.v
    upgrres.e
    upgrres.f
    upgrres.s
    uhgrspan1lem3
    eqcomi
    isusgrs
    mp1i
    mpbird
end
