include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "reflcl.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr.mm"
include "zred.mm"
include "flle.mm"
include "leadd1dd.mm"
include "1red.mm"
include "readdcld.mm"
include "flltp1.mm"
include "ltadd1dd.mm"
include "recnd.mm"
include "1cnd.mm"
include "add32d.mm"
include "breqtrd.mm"
include "wb.mm"
include "flcld.mm"
include "zaddcld.mm"
include "flbi.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem fladdz
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. ZZ ) -> ( |_ ` ( A + N ) ) = ( ( |_ ` A ) + N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    caddc
    co
    #
    cfl
    cfv
    cA
    cfl
    cfv
    #
    cN
    caddc
    co
    #
    wceq
    #
    @5
    @3
    cle
    wbr
    #
    @3
    @5
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @2
    @4
    cA
    cN
    @0
    @4
    cr
    wcel
    @1
    cA
    reflcl
    adantr
    #
    @0
    @1
    simpl
    #
    @2
    cN
    @0
    @1
    simpr
    #
    zred
    #
    @0
    @4
    cA
    cle
    wbr
    @1
    cA
    flle
    adantr
    leadd1dd
    @2
    @3
    @4
    c1
    caddc
    co
    #
    cN
    caddc
    co
    @8
    clt
    @2
    cA
    @14
    cN
    @11
    @2
    @4
    c1
    @10
    @2
    1red
    readdcld
    @13
    @0
    cA
    @14
    clt
    wbr
    @1
    cA
    flltp1
    adantr
    ltadd1dd
    @2
    @4
    c1
    cN
    @2
    @4
    @10
    recnd
    @2
    1cnd
    @2
    cN
    @13
    recnd
    add32d
    breqtrd
    @2
    @3
    cr
    wcel
    @5
    cz
    wcel
    @6
    @7
    @9
    wa
    wb
    @2
    cA
    cN
    @11
    @13
    readdcld
    @2
    @4
    cN
    @2
    cA
    @11
    flcld
    @12
    zaddcld
    @3
    @5
    flbi
    syl2anc
    mpbir2and
end
