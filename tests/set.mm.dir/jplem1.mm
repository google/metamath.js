include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cpjh.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cch.mm"
include "wb.mm"
include "pjnorm2.mm"
include "mpan.mm"
include "eqeq2.mm"
include "sylan9bb.mm"
include "sq1.mm"
include "eqeq2i.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "pjhcli.mm"
include "normcl.mm"
include "syl.mm"
include "normge0.mm"
include "1re.mm"
include "0le1.mm"
include "sq11.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "syl5bbr.mm"
include "adantr.mm"
include "bitr4d.mm"

theorem jplem1
  let vu: setvar u
  let cA: class A
  assume jplem1.1: |- A e. CH


  assert |- ( ( u e. ~H /\ ( normh ` u ) = 1 ) -> ( u e. A <-> ( ( normh ` ( ( projh ` A ) ` u ) ) ^ 2 ) = 1 ) )

  proof
    vu
    cv
    #
    chil
    wcel
    #
    @0
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    @0
    cA
    wcel
    #
    @0
    cA
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c1
    wceq
    #
    @6
    c2
    cexp
    co
    #
    c1
    wceq
    #
    @1
    @4
    @6
    @2
    wceq
    #
    @3
    @7
    cA
    cch
    wcel
    @1
    @4
    @10
    wb
    jplem1.1
    @0
    cA
    pjnorm2
    mpan
    @2
    c1
    @6
    eqeq2
    sylan9bb
    @1
    @9
    @7
    wb
    @3
    @9
    @8
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @1
    @7
    @11
    c1
    @8
    sq1
    eqeq2i
    @1
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @12
    @7
    wb
    #
    @1
    @5
    chil
    wcel
    #
    @13
    @0
    cA
    jplem1.1
    pjhcli
    #
    @5
    normcl
    syl
    @1
    @16
    @14
    @17
    @5
    normge0
    syl
    @13
    @14
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @15
    1re
    0le1
    @6
    c1
    sq11
    mpanr12
    syl2anc
    syl5bbr
    adantr
    bitr4d
end
