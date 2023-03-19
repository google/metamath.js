include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "wrex.mm"
include "cmo.mm"
include "lgsqr.mm"
include "cn.mm"
include "wb.mm"
include "eldifi.mm"
include "prmnn.mm"
include "syl.mm"
include "ad2antlr.mm"
include "zsqcl.mm"
include "adantl.mm"
include "simpll.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "biimprd.mm"
include "reximdva.mm"
include "adantld.mm"
include "sylbid.mm"

theorem lgsqrmod
  let vx: setvar x
  let cA: class A
  let cP: class P

  disjoint A x
  disjoint P x
  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( ( A /L P ) = 1 -> E. x e. ZZ ( ( x ^ 2 ) mod P ) = ( A mod P ) ) )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cA
    cP
    clgs
    co
    c1
    wceq
    cP
    cA
    cdvds
    wbr
    wn
    #
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cmin
    co
    cdvds
    wbr
    #
    vx
    cz
    wrex
    #
    wa
    @6
    cP
    cmo
    co
    cA
    cP
    cmo
    co
    wceq
    #
    vx
    cz
    wrex
    #
    vx
    cA
    cP
    lgsqr
    @3
    @8
    @10
    @4
    @3
    @7
    @9
    vx
    cz
    @3
    @5
    cz
    wcel
    #
    wa
    #
    @9
    @7
    @12
    cP
    cn
    wcel
    #
    @6
    cz
    wcel
    #
    @0
    @9
    @7
    wb
    @2
    @13
    @0
    @11
    @2
    cP
    cprime
    wcel
    @13
    cP
    cprime
    @1
    eldifi
    cP
    prmnn
    syl
    ad2antlr
    @11
    @14
    @3
    @5
    zsqcl
    adantl
    @0
    @2
    @11
    simpll
    @6
    cA
    cP
    moddvds
    syl3anc
    biimprd
    reximdva
    adantld
    sylbid
end
