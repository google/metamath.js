include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
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
include "crn.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "mp1i.mm"
include "eqidd.mm"
include "dmresi.mm"
include "a1i.mm"
include "f1eq123d.mm"
include "mpbird.mm"
include "cumgr.mm"
include "usgrumgr.mm"
include "umgrres1lem.mm"
include "sylan.mm"
include "f1ssr.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "cvtx.mm"
include "upgrres1lem2.mm"
include "eqcomi.mm"
include "ciedg.mm"
include "upgrres1lem3.mm"
include "isusgrs.mm"

theorem usgrres1
  let cS: class S
  let ve: setvar e
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  let vx: setvar x
  assume upgrres1.v: |- V = ( Vtx ` G )
  assume upgrres1.e: |- E = ( Edg ` G )
  assume upgrres1.f: |- F = { e e. E | N e/ e }
  assume upgrres1.s: |- S = <. ( V \ { N } ) , ( _I |` F ) >.

  disjoint E e
  disjoint G e
  disjoint N e
  disjoint V e
  disjoint F p
  disjoint G p
  disjoint N p
  disjoint V p
  disjoint e p
  disjoint G x
  disjoint p x
  disjoint S p
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
    cid
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
    @5
    cF
    @4
    wf1
    #
    @4
    crn
    @7
    wss
    #
    @8
    @2
    @9
    cF
    cF
    @4
    wf1
    #
    cF
    cF
    @4
    wf1o
    @11
    @2
    cF
    f1oi
    cF
    cF
    @4
    f1of1
    mp1i
    @2
    @5
    cF
    cF
    cF
    @4
    @4
    @2
    @4
    eqidd
    @5
    cF
    wceq
    @2
    cF
    dmresi
    a1i
    @2
    cF
    eqidd
    f1eq123d
    mpbird
    @0
    cG
    cumgr
    wcel
    @1
    @10
    cG
    usgrumgr
    ve
    cE
    cF
    cG
    cN
    cV
    vp
    upgrres1.v
    upgrres1.e
    upgrres1.f
    umgrres1lem
    sylan
    @5
    cF
    @7
    @4
    f1ssr
    syl2anc
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
    upgrres1.s
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
    ve
    cE
    cF
    cG
    cN
    cV
    upgrres1.v
    upgrres1.e
    upgrres1.f
    upgrres1.s
    upgrres1lem2
    eqcomi
    cS
    ciedg
    cfv
    @4
    cS
    ve
    cE
    cF
    cG
    cN
    cV
    upgrres1.v
    upgrres1.e
    upgrres1.f
    upgrres1.s
    upgrres1lem3
    eqcomi
    isusgrs
    mp1i
    mpbird
end
