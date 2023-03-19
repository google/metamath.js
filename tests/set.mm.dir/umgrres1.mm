include "cumgr.mm"
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
include "wf.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "dmresi.mm"
include "a1i.mm"
include "feq2d.mm"
include "mpbird.mm"
include "crn.mm"
include "rnresi.mm"
include "umgrres1lem.mm"
include "syl5eqssr.mm"
include "fssd.mm"
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
include "isumgrs.mm"

theorem umgrres1
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
  assert |- ( ( G e. UMGraph /\ N e. V ) -> S e. UMGraph )

  proof
    cG
    cumgr
    wcel
    cN
    cV
    wcel
    wa
    #
    cS
    cumgr
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
    @2
    wf
    #
    @0
    @3
    cF
    @5
    @2
    @0
    @3
    cF
    @2
    wf
    cF
    cF
    @2
    wf
    #
    cF
    cF
    @2
    wf1o
    @7
    @0
    cF
    f1oi
    cF
    cF
    @2
    f1of
    mp1i
    @0
    @3
    cF
    cF
    @2
    @3
    cF
    wceq
    @0
    cF
    dmresi
    a1i
    feq2d
    mpbird
    @0
    cF
    @2
    crn
    @5
    cF
    rnresi
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
    syl5eqssr
    fssd
    cS
    cvv
    wcel
    @1
    @6
    wb
    @0
    cS
    @4
    @2
    cop
    cvv
    upgrres1.s
    @4
    @2
    opex
    eqeltri
    vp
    cvv
    @2
    cS
    @4
    cS
    cvtx
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
    upgrres1lem2
    eqcomi
    cS
    ciedg
    cfv
    @2
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
    isumgrs
    mp1i
    mpbird
end
