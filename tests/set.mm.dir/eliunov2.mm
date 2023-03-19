include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wb.mm"
include "wi.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "wral.mm"
include "simpr.mm"
include "ovex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eleq2.mm"
include "eliun.mm"
include "a1i.mm"
include "sylan9bb.mm"
include "mpancom.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "bibi1d.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem eliunov2
  let cC: class C
  let cR: class R
  let cU: class U
  let vn: setvar n
  let c.ex: class .^
  let cN: class N
  let cV: class V
  let cX: class X
  let vr: setvar r
  assume mptiunov2.def: |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) )

  disjoint n r
  disjoint R n
  disjoint R r
  disjoint X n
  disjoint n r
  disjoint C n
  disjoint N n
  disjoint .^ n
  disjoint C r
  disjoint N r
  disjoint .^ r
  disjoint C N
  disjoint .^ C
  disjoint .^ N
  assert |- ( ( R e. U /\ N e. V ) -> ( X e. ( C ` R ) <-> E. n e. N X e. ( R .^ n ) ) )

  proof
    cR
    cU
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    cX
    cR
    cC
    cfv
    #
    wcel
    #
    cX
    cR
    vn
    cv
    #
    c.ex
    co
    #
    wcel
    vn
    cN
    wrex
    #
    wb
    #
    wi
    #
    @2
    cX
    cR
    vr
    cvv
    vn
    cN
    vr
    cv
    #
    @5
    c.ex
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    wcel
    #
    @7
    wb
    #
    wi
    #
    @14
    vn
    cN
    @6
    ciun
    #
    wceq
    #
    @2
    @16
    @2
    cR
    cvv
    wcel
    #
    @18
    cvv
    wcel
    #
    @19
    @0
    @20
    @1
    cR
    cU
    elex
    adantr
    @2
    @1
    @6
    cvv
    wcel
    #
    vn
    cN
    wral
    @21
    @0
    @1
    simpr
    @22
    vn
    cN
    cR
    @5
    c.ex
    ovex
    rgenw
    vn
    cN
    @6
    cV
    cvv
    iunexg
    sylancl
    vr
    cR
    @12
    @18
    cvv
    cvv
    @13
    @10
    cR
    wceq
    vn
    cN
    @11
    @6
    @10
    cR
    @5
    c.ex
    oveq1
    iuneq2d
    @13
    eqid
    fvmptg
    syl2anc
    @19
    @15
    cX
    @18
    wcel
    #
    @2
    @7
    @14
    @18
    cX
    eleq2
    @23
    @7
    wb
    @2
    vn
    cX
    cN
    @6
    eliun
    a1i
    sylan9bb
    mpancom
    cC
    @13
    wceq
    #
    @9
    @17
    wb
    mptiunov2.def
    @24
    @8
    @16
    @2
    @24
    @4
    @15
    @7
    @24
    @3
    @14
    cX
    cR
    cC
    @13
    fveq1
    eleq2d
    bibi1d
    imbi2d
    ax-mp
    mpbir
end
