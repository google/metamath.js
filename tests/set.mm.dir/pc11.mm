include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cprime.mm"
include "wral.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "cle.mm"
include "cxr.mm"
include "cq.mm"
include "zq.mm"
include "pcxcl.mm"
include "sylan2.mm"
include "anim12dan.mm"
include "xrletri3.mm"
include "syl.mm"
include "ancoms.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "syl6bb.mm"
include "pc2dvds.mm"
include "anbi12d.mm"
include "bitr4d.mm"
include "syl2an.mm"
include "dvdseq.mm"
include "ex.mm"
include "sylbid.mm"
include "impbid2.mm"

theorem pc11
  let cA: class A
  let cB: class B
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y

  disjoint A p
  disjoint B p
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A = B <-> A. p e. Prime ( p pCnt A ) = ( p pCnt B ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    vp
    cv
    #
    cA
    cpc
    co
    #
    @4
    cB
    cpc
    co
    #
    wceq
    #
    vp
    cprime
    wral
    #
    @3
    @7
    vp
    cprime
    cA
    cB
    @4
    cpc
    oveq2
    ralrimivw
    @2
    @8
    cA
    cB
    cdvds
    wbr
    #
    cB
    cA
    cdvds
    wbr
    #
    wa
    #
    @3
    @0
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @8
    @11
    wb
    @1
    cA
    nn0z
    cB
    nn0z
    @12
    @13
    wa
    #
    @8
    @5
    @6
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @6
    @5
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    wa
    #
    @11
    @14
    @8
    @15
    @17
    wa
    #
    vp
    cprime
    wral
    @19
    @14
    @7
    @20
    vp
    cprime
    @4
    cprime
    wcel
    #
    @14
    @7
    @20
    wb
    #
    @21
    @14
    wa
    @5
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    wa
    @22
    @21
    @12
    @23
    @13
    @24
    @12
    @21
    cA
    cq
    wcel
    @23
    cA
    zq
    @4
    cA
    pcxcl
    sylan2
    @13
    @21
    cB
    cq
    wcel
    @24
    cB
    zq
    @4
    cB
    pcxcl
    sylan2
    anim12dan
    @5
    @6
    xrletri3
    syl
    ancoms
    ralbidva
    @15
    @17
    vp
    cprime
    r19.26
    syl6bb
    @14
    @9
    @16
    @10
    @18
    cA
    cB
    vp
    pc2dvds
    @13
    @12
    @10
    @18
    wb
    cB
    cA
    vp
    pc2dvds
    ancoms
    anbi12d
    bitr4d
    syl2an
    @2
    @11
    @3
    cA
    cB
    dvdseq
    ex
    sylbid
    impbid2
end
