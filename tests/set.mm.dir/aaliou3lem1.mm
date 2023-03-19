include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "cr.mm"
include "wceq.mm"
include "cv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "crp.mm"
include "cz.mm"
include "2rp.mm"
include "cn0.mm"
include "simpl.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "syl.mm"
include "nnzd.mm"
include "znegcld.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "halfre.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "eluzelz.mm"
include "nnz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "rpmulcld.mm"
include "rpred.mm"
include "eqeltrd.mm"

theorem aaliou3lem1
  let cA: class A
  let cB: class B
  let cG: class G
  let vc: setvar c
  let cF: class F
  let vb: setvar b
  let vd: setvar d
  let va: setvar a
  assume aaliou3lem.a: |- G = ( c e. ( ZZ>= ` A ) |-> ( ( 2 ^ -u ( ! ` A ) ) x. ( ( 1 / 2 ) ^ ( c - A ) ) ) )

  disjoint A c
  disjoint B c
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A a
  disjoint A b
  disjoint A d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint G a
  disjoint G b
  disjoint G d
  assert |- ( ( A e. NN /\ B e. ( ZZ>= ` A ) ) -> ( G ` B ) e. RR )

  proof
    cA
    cn
    wcel
    #
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    cB
    cG
    cfv
    #
    c2
    cA
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    c1
    c2
    cdiv
    co
    #
    cB
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cr
    @2
    @4
    @11
    wceq
    @0
    vc
    cB
    @7
    @8
    vc
    cv
    #
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    @11
    @1
    cG
    @12
    cB
    wceq
    #
    @14
    @10
    @7
    cmul
    @15
    @13
    @9
    @8
    cexp
    @12
    cB
    cA
    cmin
    oveq1
    oveq2d
    oveq2d
    aaliou3lem.a
    @7
    @10
    cmul
    ovex
    fvmpt
    adantl
    @3
    @11
    @3
    @7
    @10
    @3
    c2
    crp
    wcel
    @6
    cz
    wcel
    @7
    crp
    wcel
    2rp
    @3
    @5
    @3
    @5
    @3
    cA
    cn0
    wcel
    @5
    cn
    wcel
    @3
    cA
    @0
    @2
    simpl
    nnnn0d
    cA
    faccl
    syl
    nnzd
    znegcld
    c2
    @6
    rpexpcl
    sylancr
    @3
    @8
    crp
    wcel
    @9
    cz
    wcel
    #
    @10
    crp
    wcel
    @8
    halfre
    halfgt0
    elrpii
    @2
    cB
    cz
    wcel
    cA
    cz
    wcel
    @16
    @0
    cA
    cB
    eluzelz
    cA
    nnz
    cB
    cA
    zsubcl
    syl2anr
    @8
    @9
    rpexpcl
    sylancr
    rpmulcld
    rpred
    eqeltrd
end
