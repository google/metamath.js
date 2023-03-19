include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cbl.mm"
include "co.mm"
include "wceq.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "wi.mm"
include "simprrr.mm"
include "cxr.mm"
include "simplll.mm"
include "simplr.mm"
include "simprlr.mm"
include "rpxrd.mm"
include "simprll.mm"
include "simprrl.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "eqsstr3d.mm"
include "simpllr.mm"
include "eqsstrd.mm"
include "jca.mm"
include "expr.mm"
include "anassrs.mm"
include "reximdva.mm"
include "r19.40.mm"
include "syl6.mm"
include "ralimdva.mm"
include "r19.26.mm"
include "syl6ib.mm"
include "metequiv.mm"
include "sylibrd.mm"

theorem metequiv2
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cS: class S
  let wph: wff ph
  let va: setvar a
  let vb: setvar b
  assume metequiv.3: |- J = ( MetOpen ` C )
  assume metequiv.4: |- K = ( MetOpen ` D )

  disjoint r s
  disjoint r x
  disjoint C r
  disjoint s x
  disjoint C s
  disjoint C x
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint K r
  disjoint K s
  disjoint K x
  disjoint D r
  disjoint D s
  disjoint D x
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint r y
  disjoint r z
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J y
  disjoint K y
  disjoint R s
  disjoint R y
  disjoint S y
  disjoint D y
  disjoint D z
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint X y
  disjoint X z
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint X a
  disjoint X b
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` X ) ) -> ( A. x e. X A. r e. RR+ E. s e. RR+ ( s <_ r /\ ( x ( ball ` C ) s ) = ( x ( ball ` D ) s ) ) -> J = K ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    vs
    cv
    #
    vr
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @4
    cC
    cbl
    cfv
    #
    co
    #
    @7
    @4
    cD
    cbl
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vx
    cX
    wral
    @11
    @7
    @5
    @8
    co
    #
    wss
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    @9
    @7
    @5
    @10
    co
    #
    wss
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    wa
    #
    vx
    cX
    wral
    cJ
    cK
    wceq
    @3
    @15
    @22
    vx
    cX
    @3
    @7
    cX
    wcel
    #
    wa
    #
    @15
    @18
    @21
    wa
    #
    vr
    crp
    wral
    @22
    @24
    @14
    @25
    vr
    crp
    @24
    @5
    crp
    wcel
    #
    wa
    #
    @14
    @17
    @20
    wa
    #
    vs
    crp
    wrex
    @25
    @27
    @13
    @28
    vs
    crp
    @24
    @26
    @4
    crp
    wcel
    #
    @13
    @28
    wi
    @24
    @26
    @29
    wa
    #
    @13
    @28
    @24
    @30
    @13
    wa
    #
    wa
    #
    @17
    @20
    @32
    @11
    @9
    @16
    @24
    @30
    @6
    @12
    simprrr
    #
    @32
    @1
    @23
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @6
    @9
    @16
    wss
    @1
    @2
    @23
    @31
    simplll
    @3
    @23
    @31
    simplr
    #
    @32
    @4
    @24
    @26
    @29
    @13
    simprlr
    rpxrd
    #
    @32
    @5
    @24
    @26
    @29
    @13
    simprll
    rpxrd
    #
    @24
    @30
    @6
    @12
    simprrl
    #
    cC
    @7
    @4
    @5
    cX
    ssbl
    syl221anc
    eqsstr3d
    @32
    @9
    @11
    @19
    @33
    @32
    @2
    @23
    @34
    @35
    @6
    @11
    @19
    wss
    @1
    @2
    @23
    @31
    simpllr
    @36
    @37
    @38
    @39
    cD
    @7
    @4
    @5
    cX
    ssbl
    syl221anc
    eqsstrd
    jca
    expr
    anassrs
    reximdva
    @17
    @20
    vs
    crp
    r19.40
    syl6
    ralimdva
    @18
    @21
    vr
    crp
    r19.26
    syl6ib
    ralimdva
    vx
    cC
    cD
    cJ
    cK
    cX
    vs
    vr
    vr
    vs
    metequiv.3
    metequiv.4
    metequiv
    sylibrd
end
