include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "cif.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "mat1ov.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "ex.mm"
include "ralrimivva.mm"
include "dmatel.mm"
include "mpbir2and.mm"

theorem dmatid
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` A ) e. D )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cA
    cur
    cfv
    #
    cD
    wcel
    @3
    cB
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @5
    @6
    @3
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @2
    cA
    crg
    wcel
    @4
    cA
    cR
    cN
    dmatid.a
    matring
    cB
    cA
    @3
    dmatid.b
    @3
    eqid
    #
    ringidcl
    syl
    @2
    @10
    vi
    vj
    cN
    cN
    @2
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    wa
    #
    wa
    #
    @7
    @9
    @15
    @7
    @8
    @5
    @6
    wceq
    cR
    cur
    cfv
    #
    c.0
    cif
    c.0
    @15
    cA
    cR
    @3
    @16
    @5
    @6
    cN
    c.0
    dmatid.a
    @16
    eqid
    dmatid.0
    @2
    @0
    @14
    @0
    @1
    simpl
    adantr
    @2
    @1
    @14
    @0
    @1
    simpr
    adantr
    @14
    @12
    @2
    @12
    @13
    simpl
    adantl
    @14
    @13
    @2
    @12
    @13
    simpr
    adantl
    @11
    mat1ov
    @5
    @6
    @16
    c.0
    ifnefalse
    sylan9eq
    ex
    ralrimivva
    cA
    cB
    cD
    cR
    vi
    vj
    @3
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatel
    mpbir2and
end
