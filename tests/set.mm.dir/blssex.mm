include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "co.mm"
include "crp.mm"
include "wi.mm"
include "w3a.mm"
include "blss.mm"
include "sstr.mm"
include "expcom.mm"
include "reximdv.mm"
include "syl5com.mm"
include "3expa.mm"
include "expimpd.mm"
include "adantlr.mm"
include "rexlimdva.mm"
include "cxr.mm"
include "simpll.mm"
include "simplr.mm"
include "rpxr.mm"
include "ad2antrl.mm"
include "blelrn.mm"
include "syl3anc.mm"
include "simprl.mm"
include "blcntr.mm"
include "simprr.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "impbid.mm"

theorem blssex
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S

  disjoint r x
  disjoint A r
  disjoint A x
  disjoint D r
  disjoint D x
  disjoint P r
  disjoint P x
  disjoint X r
  disjoint X x
  disjoint r y
  disjoint x y
  disjoint A y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint P y
  disjoint P z
  disjoint S x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( *Met ` X ) /\ P e. X ) -> ( E. x e. ran ( ball ` D ) ( P e. x /\ x C_ A ) <-> E. r e. RR+ ( P ( ball ` D ) r ) C_ A ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cP
    vx
    cv
    #
    wcel
    #
    @3
    cA
    wss
    #
    wa
    #
    vx
    cD
    cbl
    cfv
    #
    crn
    #
    wrex
    #
    cP
    vr
    cv
    #
    @7
    co
    #
    cA
    wss
    #
    vr
    crp
    wrex
    #
    @2
    @6
    @13
    vx
    @8
    @0
    @3
    @8
    wcel
    #
    @6
    @13
    wi
    @1
    @0
    @14
    wa
    @4
    @5
    @13
    @0
    @14
    @4
    @5
    @13
    wi
    @0
    @14
    @4
    w3a
    @11
    @3
    wss
    #
    vr
    crp
    wrex
    @5
    @13
    vr
    @3
    cD
    cP
    cX
    blss
    @5
    @15
    @12
    vr
    crp
    @15
    @5
    @12
    @11
    @3
    cA
    sstr
    expcom
    reximdv
    syl5com
    3expa
    expimpd
    adantlr
    rexlimdva
    @2
    @12
    @9
    vr
    crp
    @2
    @10
    crp
    wcel
    #
    @12
    wa
    #
    wa
    #
    @11
    @8
    wcel
    #
    cP
    @11
    wcel
    #
    @12
    @9
    @18
    @0
    @1
    @10
    cxr
    wcel
    #
    @19
    @0
    @1
    @17
    simpll
    #
    @0
    @1
    @17
    simplr
    #
    @16
    @21
    @2
    @12
    @10
    rpxr
    ad2antrl
    cD
    cP
    @10
    cX
    blelrn
    syl3anc
    @18
    @0
    @1
    @16
    @20
    @22
    @23
    @2
    @16
    @12
    simprl
    cD
    cP
    @10
    cX
    blcntr
    syl3anc
    @2
    @16
    @12
    simprr
    @6
    @20
    @12
    wa
    vx
    @11
    @8
    @3
    @11
    wceq
    @4
    @20
    @5
    @12
    @3
    @11
    cP
    eleq2
    @3
    @11
    cA
    sseq1
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    impbid
end
