include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "cv.mm"
include "wsbc.mm"
include "wb.mm"
include "w3a.mm"
include "zsubcl.mm"
include "3adant2.mm"
include "3adant3.mm"
include "simp1.mm"
include "fzrevral.mm"
include "syl3anc.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "nncan.mm"
include "oveq12d.mm"
include "syl3an.mm"
include "raleqdv.mm"
include "bitrd.mm"
include "3coml.mm"

theorem fzrevral2
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x

  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint k ph
  disjoint j x
  disjoint k x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( A. j e. ( ( K - N ) ... ( K - M ) ) ph <-> A. k e. ( M ... N ) [. ( K - k ) / j ]. ph ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wph
    vj
    cK
    cN
    cmin
    co
    #
    cK
    cM
    cmin
    co
    #
    cfz
    co
    wral
    #
    wph
    vj
    cK
    vk
    cv
    cmin
    co
    wsbc
    #
    vk
    cM
    cN
    cfz
    co
    #
    wral
    #
    wb
    @0
    @1
    @2
    w3a
    #
    @5
    @6
    vk
    cK
    @4
    cmin
    co
    #
    cK
    @3
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    @8
    @9
    @3
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @0
    @5
    @13
    wb
    @0
    @2
    @14
    @1
    cK
    cN
    zsubcl
    3adant2
    @0
    @1
    @15
    @2
    cK
    cM
    zsubcl
    3adant3
    @0
    @1
    @2
    simp1
    wph
    vj
    vk
    cK
    @3
    @4
    fzrevral
    syl3anc
    @9
    @6
    vk
    @12
    @7
    @0
    cK
    cc
    wcel
    #
    @1
    cM
    cc
    wcel
    #
    @2
    cN
    cc
    wcel
    #
    @12
    @7
    wceq
    cK
    zcn
    cM
    zcn
    cN
    zcn
    @16
    @17
    @18
    w3a
    @10
    cM
    @11
    cN
    cfz
    @16
    @17
    @10
    cM
    wceq
    @18
    cK
    cM
    nncan
    3adant3
    @16
    @18
    @11
    cN
    wceq
    @17
    cK
    cN
    nncan
    3adant2
    oveq12d
    syl3an
    raleqdv
    bitrd
    3coml
end
