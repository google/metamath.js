include "cumgr.mm"
include "wcel.mm"
include "cv.mm"
include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cpr.mm"
include "w3a.mm"
include "wrex.mm"
include "cupgr.mm"
include "umgrupgr.mm"
include "adantr.mm"
include "simpl.mm"
include "adantl.mm"
include "simpr.mm"
include "wne.mm"
include "upgr3v3e3cycl.mm"
include "reximi.mm"
include "syl.mm"
include "syl3anc.mm"
include "ex.mm"
include "exlimdvv.mm"
include "simplll.mm"
include "df-3an.mm"
include "biimpri.mm"
include "ad4ant23.mm"
include "cc0.mm"
include "umgr3cyclex.mm"
include "3simpa.mm"
include "2eximi.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "impbid.mm"

theorem umgr3v3e3cycl
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cA: class A
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cB: class B
  let cC: class C
  assume uhgr3cyclex.v: |- V = ( Vtx ` G )
  assume uhgr3cyclex.e: |- E = ( Edg ` G )

  disjoint f p
  disjoint G f
  disjoint G p
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E f
  disjoint E p
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a p
  disjoint b c
  disjoint b f
  disjoint b p
  disjoint c f
  disjoint c p
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V f
  disjoint V p
  disjoint A f
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A p
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B p
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C p
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint V i
  disjoint V j
  disjoint V k
  assert |- ( G e. UMGraph -> ( E. f E. p ( f ( Cycles ` G ) p /\ ( # ` f ) = 3 ) <-> E. a e. V E. b e. V E. c e. V ( { a , b } e. E /\ { b , c } e. E /\ { c , a } e. E ) ) )

  proof
    cG
    cumgr
    wcel
    #
    vf
    cv
    #
    vp
    cv
    #
    cG
    ccycls
    cfv
    wbr
    #
    @1
    chash
    cfv
    c3
    wceq
    #
    wa
    #
    vp
    wex
    vf
    wex
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    cE
    wcel
    @8
    vc
    cv
    #
    cpr
    cE
    wcel
    @9
    @7
    cpr
    cE
    wcel
    w3a
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    #
    @0
    @5
    @13
    vf
    vp
    @0
    @5
    @13
    @0
    @5
    wa
    cG
    cupgr
    wcel
    #
    @3
    @4
    @13
    @0
    @14
    @5
    cG
    umgrupgr
    adantr
    @5
    @3
    @0
    @3
    @4
    simpl
    adantl
    @5
    @4
    @0
    @3
    @4
    simpr
    adantl
    @14
    @3
    @4
    w3a
    @10
    @7
    @8
    wne
    @8
    @9
    wne
    @9
    @7
    wne
    w3a
    #
    wa
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    @13
    @2
    cE
    @1
    cG
    cV
    va
    vb
    vc
    uhgr3cyclex.e
    uhgr3cyclex.v
    upgr3v3e3cycl
    @18
    @12
    va
    cV
    @17
    @11
    vb
    cV
    @16
    @10
    vc
    cV
    @10
    @15
    simpl
    reximi
    reximi
    reximi
    syl
    syl3anc
    ex
    exlimdvv
    @0
    @11
    @6
    va
    vb
    cV
    cV
    @0
    @7
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    wa
    #
    wa
    #
    @10
    @6
    vc
    cV
    @22
    @9
    cV
    wcel
    #
    wa
    #
    @10
    @6
    @24
    @10
    wa
    @0
    @19
    @20
    @23
    w3a
    #
    @10
    @6
    @0
    @21
    @23
    @10
    simplll
    @21
    @23
    @25
    @0
    @10
    @25
    @21
    @23
    wa
    @19
    @20
    @23
    df-3an
    biimpri
    ad4ant23
    @24
    @10
    simpr
    @0
    @25
    @10
    w3a
    @3
    @4
    cc0
    @2
    cfv
    @7
    wceq
    #
    w3a
    #
    vp
    wex
    vf
    wex
    @6
    @7
    @8
    @9
    vf
    cE
    cG
    cV
    vp
    uhgr3cyclex.v
    uhgr3cyclex.e
    umgr3cyclex
    @27
    @5
    vf
    vp
    @3
    @4
    @26
    3simpa
    2eximi
    syl
    syl3anc
    ex
    rexlimdva
    rexlimdvva
    impbid
end
