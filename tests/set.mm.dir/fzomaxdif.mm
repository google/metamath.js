include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "abssub.mm"
include "syl2an.mm"
include "adantr.mm"
include "fzomaxdiflem.mm"
include "eqeltrd.mm"
include "ancom1s.mm"
include "cr.mm"
include "wo.mm"
include "zred.mm"
include "letric.mm"
include "mpjaodan.mm"

theorem fzomaxdif
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( C ..^ D ) /\ B e. ( C ..^ D ) ) -> ( abs ` ( A - B ) ) e. ( 0 ..^ ( D - C ) ) )

  proof
    cA
    cC
    cD
    cfzo
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cmin
    co
    cabs
    cfv
    #
    cc0
    cD
    cC
    cmin
    co
    cfzo
    co
    #
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    @3
    @4
    wa
    @5
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    @6
    @3
    @5
    @9
    wceq
    #
    @4
    @1
    cA
    cc
    wcel
    cB
    cc
    wcel
    @10
    @2
    @1
    cA
    cA
    cC
    cD
    elfzoelz
    #
    zcnd
    @2
    cB
    cB
    cC
    cD
    elfzoelz
    #
    zcnd
    cA
    cB
    abssub
    syl2an
    adantr
    cA
    cB
    cC
    cD
    fzomaxdiflem
    eqeltrd
    @2
    @1
    @8
    @7
    cB
    cA
    cC
    cD
    fzomaxdiflem
    ancom1s
    @1
    cA
    cr
    wcel
    cB
    cr
    wcel
    @4
    @8
    wo
    @2
    @1
    cA
    @11
    zred
    @2
    cB
    @12
    zred
    cA
    cB
    letric
    syl2an
    mpjaodan
end
