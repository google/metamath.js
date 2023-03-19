include "wcel.mm"
include "wa.mm"
include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "chash.mm"
include "cwlks.mm"
include "wbr.mm"
include "copab.mm"
include "w3a.mm"
include "cvtx.mm"
include "cvv.mm"
include "1vgrex.mm"
include "adantr.mm"
include "simpl.mm"
include "syl6eleq.mm"
include "simpr.mm"
include "wksv.mm"
include "a1i.mm"
include "eqeq2.mm"
include "bi2anan9.mm"
include "biidd.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "df-wlkson.mm"
include "eqid.mm"
include "3anass.mm"
include "ancom.mm"
include "bitri.mm"
include "opabbii.mm"
include "mpt2eq123i.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "mptmpt2opabbrd.mm"
include "bitr4i.mm"
include "syl6eq.mm"

theorem wlkson
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume wlkson.v: |- V = ( Vtx ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint G f
  disjoint G p
  disjoint V f
  disjoint V p
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a p
  disjoint b f
  disjoint b g
  disjoint b p
  disjoint f g
  disjoint g p
  disjoint B a
  disjoint B b
  disjoint B g
  disjoint G a
  disjoint G b
  disjoint G g
  disjoint V g
  assert |- ( ( A e. V /\ B e. V ) -> ( A ( WalksOn ` G ) B ) = { <. f , p >. | ( f ( Walks ` G ) p /\ ( p ` 0 ) = A /\ ( p ` ( # ` f ) ) = B ) } )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    cB
    cG
    cwlkson
    cfv
    co
    cc0
    vp
    cv
    #
    cfv
    #
    cA
    wceq
    #
    vf
    cv
    #
    chash
    cfv
    @3
    cfv
    #
    cB
    wceq
    #
    wa
    #
    @6
    @3
    cG
    cwlks
    cfv
    wbr
    #
    wa
    #
    vf
    vp
    copab
    @10
    @5
    @8
    w3a
    #
    vf
    vp
    copab
    @2
    @10
    @4
    va
    cv
    #
    wceq
    #
    @7
    vb
    cv
    #
    wceq
    #
    wa
    #
    @9
    @17
    cvtx
    cvtx
    cwlks
    vf
    vg
    vp
    cG
    cwlkson
    cvv
    cvv
    cA
    cB
    va
    vb
    @0
    cG
    cvv
    wcel
    @1
    cG
    cA
    cV
    wlkson.v
    1vgrex
    adantr
    @2
    cA
    cV
    cG
    cvtx
    cfv
    #
    @0
    @1
    simpl
    wlkson.v
    syl6eleq
    @2
    cB
    cV
    @18
    @0
    @1
    simpr
    wlkson.v
    syl6eleq
    @10
    vf
    vp
    copab
    cvv
    wcel
    @2
    vf
    cG
    vp
    wksv
    a1i
    @2
    @10
    simpr
    @13
    cA
    wceq
    @14
    @5
    @15
    cB
    wceq
    @16
    @8
    @13
    cA
    @4
    eqeq2
    @15
    cB
    @7
    eqeq2
    bi2anan9
    vg
    cv
    #
    cG
    wceq
    @17
    biidd
    cwlkson
    vg
    cvv
    va
    vb
    @19
    cvtx
    cfv
    #
    @20
    @6
    @3
    @19
    cwlks
    cfv
    wbr
    #
    @14
    @16
    w3a
    #
    vf
    vp
    copab
    #
    cmpt2
    #
    cmpt
    vg
    cvv
    va
    vb
    @20
    @20
    @17
    @21
    wa
    #
    vf
    vp
    copab
    #
    cmpt2
    #
    cmpt
    vf
    vg
    vp
    va
    vb
    df-wlkson
    vg
    cvv
    @24
    @27
    va
    vb
    @20
    @20
    @23
    @20
    @20
    @26
    @20
    eqid
    #
    @28
    @22
    @25
    vf
    vp
    @22
    @21
    @17
    wa
    @25
    @21
    @14
    @16
    3anass
    @21
    @17
    ancom
    bitri
    opabbii
    mpt2eq123i
    mpteq2i
    eqtri
    mptmpt2opabbrd
    @11
    @12
    vf
    vp
    @11
    @10
    @9
    wa
    @12
    @9
    @10
    ancom
    @10
    @5
    @8
    3anass
    bitr4i
    opabbii
    syl6eq
end
