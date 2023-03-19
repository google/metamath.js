include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "wsbc.mm"
include "caddc.mm"
include "wceq.mm"
include "fzoval.mm"
include "3ad2ant2.mm"
include "raleqdv.mm"
include "wb.mm"
include "peano2zm.mm"
include "fzshftral.mm"
include "syl3an2.mm"
include "zaddcl.mm"
include "3adant1.mm"
include "syl.mm"
include "wa.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "adantl.mm"
include "1cnd.mm"
include "addsubd.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "3bitrd.mm"

theorem fzoshftral
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N

  disjoint K j
  disjoint K k
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint k ph
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( A. j e. ( M ..^ N ) ph <-> A. k e. ( ( M + K ) ..^ ( N + K ) ) [. ( k - K ) / j ]. ph ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    wph
    vj
    cM
    cN
    cfzo
    co
    #
    wral
    wph
    vj
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wph
    vj
    vk
    cv
    cK
    cmin
    co
    wsbc
    #
    vk
    cM
    cK
    caddc
    co
    #
    @5
    cK
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    @8
    vk
    @9
    cN
    cK
    caddc
    co
    #
    cfzo
    co
    #
    wral
    @3
    wph
    vj
    @4
    @6
    @1
    @0
    @4
    @6
    wceq
    @2
    cM
    cN
    fzoval
    3ad2ant2
    raleqdv
    @1
    @0
    @5
    cz
    wcel
    @2
    @7
    @12
    wb
    cN
    peano2zm
    wph
    vj
    vk
    cK
    cM
    @5
    fzshftral
    syl3an2
    @3
    @8
    vk
    @11
    @14
    @3
    @14
    @9
    @13
    c1
    cmin
    co
    #
    cfz
    co
    #
    @11
    @3
    @13
    cz
    wcel
    #
    @14
    @16
    wceq
    @1
    @2
    @17
    @0
    cN
    cK
    zaddcl
    3adant1
    @9
    @13
    fzoval
    syl
    @3
    @15
    @10
    @9
    cfz
    @1
    @2
    @15
    @10
    wceq
    @0
    @1
    @2
    wa
    #
    cN
    cK
    c1
    @1
    cN
    cc
    wcel
    @2
    cN
    zcn
    adantr
    @2
    cK
    cc
    wcel
    @1
    cK
    zcn
    adantl
    @18
    1cnd
    addsubd
    3adant1
    oveq2d
    eqtr2d
    raleqdv
    3bitrd
end
