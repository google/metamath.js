include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cmul.mm"
include "clgs.mm"
include "c2.mm"
include "cexp.mm"
include "cc0.mm"
include "wne.mm"
include "simp1.mm"
include "nnz.mm"
include "3ad2ant2.mm"
include "nnne0.mm"
include "lgsdi.mm"
include "syl32anc.mm"
include "cc.mm"
include "nncn.mm"
include "sqvald.mm"
include "oveq2d.mm"
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
include "sylan2.mm"
include "biimp3ar.mm"
include "oveq1d.mm"
include "sq1.mm"
include "syl6eq.mm"
include "zcnd.mm"
include "3eqtr3d.mm"
include "3eqtr4d.mm"

theorem lgssq2
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


  assert |- ( ( A e. ZZ /\ N e. NN /\ ( A gcd N ) = 1 ) -> ( A /L ( N ^ 2 ) ) = 1 )

  proof
    cA
    cz
    wcel
    #
    cN
    cn
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
    cN
    cN
    cmul
    co
    #
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    @6
    cmul
    co
    #
    cA
    cN
    c2
    cexp
    co
    #
    clgs
    co
    c1
    @3
    @0
    cN
    cz
    wcel
    #
    @9
    cN
    cc0
    wne
    #
    @10
    @5
    @7
    wceq
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    @9
    @2
    cN
    nnz
    #
    3ad2ant2
    #
    @13
    @1
    @0
    @10
    @2
    cN
    nnne0
    3ad2ant2
    #
    @14
    cA
    cN
    cN
    lgsdi
    syl32anc
    @3
    @8
    @4
    cA
    clgs
    @3
    cN
    @1
    @0
    cN
    cc
    wcel
    @2
    cN
    nncn
    3ad2ant2
    sqvald
    oveq2d
    @3
    @6
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @6
    c2
    cexp
    co
    #
    c1
    @7
    @3
    @6
    cr
    wcel
    @16
    @17
    wceq
    @3
    @6
    @3
    @0
    @9
    @6
    cz
    wcel
    @11
    @13
    cA
    cN
    lgscl
    syl2anc
    #
    zred
    @6
    absresq
    syl
    @3
    @16
    c1
    c2
    cexp
    co
    c1
    @3
    @15
    c1
    c2
    cexp
    @0
    @1
    @15
    c1
    wceq
    #
    @2
    @1
    @0
    @9
    @19
    @2
    wb
    @12
    cA
    cN
    lgsabs1
    sylan2
    biimp3ar
    oveq1d
    sq1
    syl6eq
    @3
    @6
    @3
    @6
    @18
    zcnd
    sqvald
    3eqtr3d
    3eqtr4d
end
