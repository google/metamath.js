include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "wb.mm"
include "moddvds.mm"
include "3coml.mm"
include "simp3.mm"
include "nnzd.mm"
include "zsubcl.mm"
include "3adant3.mm"
include "divides.mm"
include "syl2anc.mm"
include "bitrd.mm"

theorem congr
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cM: class M

  disjoint A n
  disjoint B n
  disjoint M n
  assert |- ( ( A e. ZZ /\ B e. ZZ /\ M e. NN ) -> ( ( A mod M ) = ( B mod M ) <-> E. n e. ZZ ( n x. M ) = ( A - B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cM
    cn
    wcel
    #
    w3a
    #
    cA
    cM
    cmo
    co
    cB
    cM
    cmo
    co
    wceq
    #
    cM
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cv
    cM
    cmul
    co
    @5
    wceq
    vn
    cz
    wrex
    #
    @2
    @0
    @1
    @4
    @6
    wb
    cA
    cB
    cM
    moddvds
    3coml
    @3
    cM
    cz
    wcel
    @5
    cz
    wcel
    #
    @6
    @7
    wb
    @3
    cM
    @0
    @1
    @2
    simp3
    nnzd
    @0
    @1
    @8
    @2
    cA
    cB
    zsubcl
    3adant3
    vn
    cM
    @5
    divides
    syl2anc
    bitrd
end
