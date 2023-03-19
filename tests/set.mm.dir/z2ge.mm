include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "wrex.mm"
include "ifcl.mm"
include "ancoms.mm"
include "cr.mm"
include "zre.mm"
include "max1.mm"
include "max2.mm"
include "jca.mm"
include "syl2an.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem z2ge
  let vk: setvar k
  let cM: class M
  let cN: class N

  disjoint M k
  disjoint N k
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> E. k e. ZZ ( M <_ k /\ N <_ k ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cz
    wcel
    #
    cM
    @3
    cle
    wbr
    #
    cN
    @3
    cle
    wbr
    #
    wa
    #
    cM
    vk
    cv
    #
    cle
    wbr
    #
    cN
    @8
    cle
    wbr
    #
    wa
    #
    vk
    cz
    wrex
    @1
    @0
    @4
    @2
    cN
    cM
    cz
    ifcl
    ancoms
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @7
    @1
    cM
    zre
    cN
    zre
    @12
    @13
    wa
    @5
    @6
    cM
    cN
    max1
    cM
    cN
    max2
    jca
    syl2an
    @11
    @7
    vk
    @3
    cz
    @8
    @3
    wceq
    @9
    @5
    @10
    @6
    @8
    @3
    cM
    cle
    breq2
    @8
    @3
    cN
    cle
    breq2
    anbi12d
    rspcev
    syl2anc
end
