include "cumgr.mm"
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
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cuhgr.mm"
include "wfun.mm"
include "umgruhgr.mm"
include "uhgrfun.mm"
include "funres.mm"
include "3syl.mm"
include "funfnd.mm"
include "adantr.mm"
include "umgrreslem.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "cvv.mm"
include "wb.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "cvtx.mm"
include "uhgrspan1lem2.mm"
include "eqcomi.mm"
include "ciedg.mm"
include "uhgrspan1lem3.mm"
include "isumgrs.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem umgrres
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vj: setvar j
  let vp: setvar p
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
  assert |- ( ( G e. UMGraph /\ N e. V ) -> S e. UMGraph )

  proof
    cG
    cumgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cS
    cumgr
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
    wf
    #
    @2
    @4
    @5
    wfn
    #
    @4
    crn
    @7
    wss
    @8
    @0
    @9
    @1
    @0
    @4
    @0
    cG
    cuhgr
    wcel
    cE
    wfun
    @4
    wfun
    cG
    umgruhgr
    cE
    cG
    upgrres.e
    uhgrfun
    cF
    cE
    funres
    3syl
    funfnd
    adantr
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
    @5
    @7
    @4
    df-f
    sylanbrc
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
    isumgrs
    mp1i
    mpbird
end
