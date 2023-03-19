include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cabs.mm"
include "cfv.mm"
include "gcdabs.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "cn0.mm"
include "wceq.mm"
include "nn0abscl.mm"
include "nn0gcdsq.mm"
include "syl2an.mm"
include "cr.mm"
include "zre.mm"
include "adantr.mm"
include "absresq.mm"
include "syl.mm"
include "adantl.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem zgcdsq
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A gcd B ) ^ 2 ) = ( ( A ^ 2 ) gcd ( B ^ 2 ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cgcd
    co
    #
    c2
    cexp
    co
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    cgcd
    co
    #
    c2
    cexp
    co
    #
    @4
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    cgcd
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cgcd
    co
    @2
    @3
    @6
    c2
    cexp
    @2
    @6
    @3
    cA
    cB
    gcdabs
    eqcomd
    oveq1d
    @0
    @4
    cn0
    wcel
    @5
    cn0
    wcel
    @7
    @10
    wceq
    @1
    cA
    nn0abscl
    cB
    nn0abscl
    @4
    @5
    nn0gcdsq
    syl2an
    @2
    @8
    @11
    @9
    @12
    cgcd
    @2
    cA
    cr
    wcel
    #
    @8
    @11
    wceq
    @0
    @13
    @1
    cA
    zre
    adantr
    cA
    absresq
    syl
    @2
    cB
    cr
    wcel
    #
    @9
    @12
    wceq
    @1
    @14
    @0
    cB
    zre
    adantl
    cB
    absresq
    syl
    oveq12d
    3eqtrd
end
