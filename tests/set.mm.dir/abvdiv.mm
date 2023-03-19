include "cdr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpll.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eqid.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "abvmul.mm"
include "abvrec.mm"
include "3adantr1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "cui.mm"
include "wb.mm"
include "drngunit.mm"
include "syl.mm"
include "mpbir2and.mm"
include "dvrval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "cr.mm"
include "abvcl.mm"
include "recnd.mm"
include "cc0.mm"
include "abvne0.mm"
include "divrecd.mm"
include "3eqtr4d.mm"

theorem abvdiv
  let cA: class A
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abvneg.b: |- B = ( Base ` R )
  assume abvrec.z: |- .0. = ( 0g ` R )
  assume abvdiv.p: |- ./ = ( /r ` R )


  assert |- ( ( ( R e. DivRing /\ F e. A ) /\ ( X e. B /\ Y e. B /\ Y =/= .0. ) ) -> ( F ` ( X ./ Y ) ) = ( ( F ` X ) / ( F ` Y ) ) )

  proof
    cR
    cdr
    wcel
    #
    cF
    cA
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cY
    c.0
    wne
    #
    w3a
    #
    wa
    #
    cX
    cY
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    c1
    cY
    cF
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cX
    cY
    c.dv
    co
    #
    cF
    cfv
    @13
    @14
    cdiv
    co
    @7
    @12
    @13
    @9
    cF
    cfv
    #
    cmul
    co
    #
    @16
    @7
    @1
    @3
    @9
    cB
    wcel
    #
    @12
    @19
    wceq
    @0
    @1
    @6
    simplr
    #
    @2
    @3
    @4
    @5
    simpr1
    #
    @7
    @0
    @4
    @5
    @20
    @0
    @1
    @6
    simpll
    #
    @2
    @3
    @4
    @5
    simpr2
    #
    @2
    @3
    @4
    @5
    simpr3
    #
    cB
    cR
    @8
    cY
    c.0
    abvneg.b
    abvrec.z
    @8
    eqid
    #
    drnginvrcl
    syl3anc
    cA
    cB
    cR
    @10
    cF
    cX
    @9
    abv0.a
    abvneg.b
    @10
    eqid
    #
    abvmul
    syl3anc
    @7
    @18
    @15
    @13
    cmul
    @2
    @4
    @5
    @18
    @15
    wceq
    @3
    cA
    cB
    cR
    cF
    @8
    cY
    c.0
    abv0.a
    abvneg.b
    abvrec.z
    @26
    abvrec
    3adantr1
    oveq2d
    eqtrd
    @7
    @17
    @11
    cF
    @7
    @3
    cY
    cR
    cui
    cfv
    #
    wcel
    #
    @17
    @11
    wceq
    @22
    @7
    @29
    @4
    @5
    @24
    @25
    @7
    @0
    @29
    @4
    @5
    wa
    wb
    @23
    cB
    cR
    @28
    cY
    c.0
    abvneg.b
    @28
    eqid
    #
    abvrec.z
    drngunit
    syl
    mpbir2and
    cB
    c.dv
    cR
    @10
    @28
    @8
    cX
    cY
    abvneg.b
    @27
    @30
    @26
    abvdiv.p
    dvrval
    syl2anc
    fveq2d
    @7
    @13
    @14
    @7
    @13
    @7
    @1
    @3
    @13
    cr
    wcel
    @21
    @22
    cA
    cB
    cR
    cF
    cX
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @7
    @14
    @7
    @1
    @4
    @14
    cr
    wcel
    @21
    @24
    cA
    cB
    cR
    cF
    cY
    abv0.a
    abvneg.b
    abvcl
    syl2anc
    recnd
    @7
    @1
    @4
    @5
    @14
    cc0
    wne
    @21
    @24
    @25
    cA
    cB
    cR
    cF
    cY
    c.0
    abv0.a
    abvneg.b
    abvrec.z
    abvne0
    syl3anc
    divrecd
    3eqtr4d
end
