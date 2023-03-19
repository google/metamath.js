include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "crio.mm"
include "cbr.mm"
include "ccnv.mm"
include "wa.mm"
include "wf1o.mm"
include "wi.mm"
include "bra11.mm"
include "f1ocnvfv.mm"
include "mpan.mm"
include "imp.mm"
include "oveq2d.mm"
include "adantll.mm"
include "braval.mm"
include "ancoms.mm"
include "adantr.mm"
include "fveq1.mm"
include "adantl.mm"
include "3eqtr2rd.mm"
include "wrex.mm"
include "crn.mm"
include "rnbra.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "sylbb1.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "wreu.mm"
include "f1ocnvdm.mm"
include "riesz4.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem cnvbraval
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint T t
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint t z
  assert |- ( T e. ( LinFn i^i ContFn ) -> ( `' bra ` T ) = ( iota_ y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) ) )

  proof
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    #
    @2
    vy
    cv
    #
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    vy
    chil
    crio
    #
    cT
    cbr
    ccnv
    cfv
    #
    @1
    @3
    @2
    @9
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    @8
    @9
    wceq
    #
    @1
    @11
    vx
    chil
    @1
    @2
    chil
    wcel
    #
    wa
    #
    @4
    cbr
    cfv
    #
    cT
    wceq
    #
    @11
    vy
    chil
    @15
    @4
    chil
    wcel
    #
    wa
    #
    @17
    wa
    @10
    @5
    @2
    @16
    cfv
    #
    @3
    @18
    @17
    @10
    @5
    wceq
    @15
    @18
    @17
    wa
    @9
    @4
    @2
    csp
    @18
    @17
    @9
    @4
    wceq
    #
    chil
    @0
    cbr
    wf1o
    #
    @18
    @17
    @21
    wi
    bra11
    chil
    @0
    @4
    cT
    cbr
    f1ocnvfv
    mpan
    imp
    oveq2d
    adantll
    @19
    @20
    @5
    wceq
    #
    @17
    @14
    @18
    @23
    @1
    @18
    @14
    @23
    @4
    @2
    braval
    ancoms
    adantll
    adantr
    @17
    @20
    @3
    wceq
    @19
    @2
    @16
    cT
    fveq1
    adantl
    3eqtr2rd
    @1
    @17
    vy
    chil
    wrex
    #
    @14
    cT
    cbr
    crn
    #
    wcel
    #
    @1
    @24
    @25
    @0
    cT
    rnbra
    eleq2i
    cbr
    chil
    wfn
    #
    @26
    @24
    wb
    chil
    @0
    cbr
    wf
    #
    @27
    @22
    @28
    bra11
    chil
    @0
    cbr
    f1of
    ax-mp
    chil
    @0
    cbr
    ffn
    ax-mp
    vy
    chil
    cT
    cbr
    fvelrnb
    ax-mp
    sylbb1
    adantr
    r19.29a
    ralrimiva
    @1
    @9
    chil
    wcel
    #
    @7
    vy
    chil
    wreu
    @12
    @13
    wb
    @22
    @1
    @29
    bra11
    chil
    @0
    cT
    cbr
    f1ocnvdm
    mpan
    vy
    vx
    cT
    riesz4
    @7
    @12
    vy
    chil
    @9
    @4
    @9
    wceq
    #
    @6
    @11
    vx
    chil
    @30
    @5
    @10
    @3
    @4
    @9
    @2
    csp
    oveq2
    eqeq2d
    ralbidv
    riota2
    syl2anc
    mpbid
    eqcomd
end
