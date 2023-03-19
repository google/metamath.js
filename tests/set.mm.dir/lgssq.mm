include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cmul.mm"
include "clgs.mm"
include "c2.mm"
include "cexp.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp1r.mm"
include "lgsdir.mm"
include "syl32anc.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "cabs.mm"
include "cfv.mm"
include "cr.mm"
include "lgscl.mm"
include "syl2anc.mm"
include "zred.mm"
include "absresq.mm"
include "syl.mm"
include "wb.mm"
include "lgsabs1.mm"
include "adantlr.mm"
include "biimp3ar.mm"
include "sq1.mm"
include "syl6eq.mm"
include "zcnd.mm"
include "3eqtr3d.mm"
include "3eqtr4d.mm"

theorem lgssq
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p


  assert |- ( ( ( A e. ZZ /\ A =/= 0 ) /\ N e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( A ^ 2 ) /L N ) = 1 )

  proof
    cA
    cz
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cN
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    cA
    cA
    cmul
    co
    #
    cN
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    @8
    cmul
    co
    #
    cA
    c2
    cexp
    co
    #
    cN
    clgs
    co
    c1
    @5
    @0
    @0
    @3
    @1
    @1
    @7
    @9
    wceq
    @0
    @1
    @3
    @4
    simp1l
    #
    @11
    @2
    @3
    @4
    simp2
    #
    @0
    @1
    @3
    @4
    simp1r
    #
    @13
    cA
    cA
    cN
    lgsdir
    syl32anc
    @5
    @10
    @6
    cN
    clgs
    @5
    cA
    @2
    @3
    cA
    cc
    wcel
    #
    @4
    @0
    @14
    @1
    cA
    zcn
    adantr
    3ad2ant1
    sqvald
    oveq1d
    @5
    @8
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    c1
    @9
    @5
    @8
    cr
    wcel
    @16
    @17
    wceq
    @5
    @8
    @5
    @0
    @3
    @8
    cz
    wcel
    @11
    @12
    cA
    cN
    lgscl
    syl2anc
    #
    zred
    @8
    absresq
    syl
    @5
    @16
    c1
    c2
    cexp
    co
    c1
    @5
    @15
    c1
    c2
    cexp
    @2
    @3
    @15
    c1
    wceq
    #
    @4
    @0
    @3
    @19
    @4
    wb
    @1
    cA
    cN
    lgsabs1
    adantlr
    biimp3ar
    oveq1d
    sq1
    syl6eq
    @5
    @8
    @5
    @8
    @18
    zcnd
    sqvald
    3eqtr3d
    3eqtr4d
end
