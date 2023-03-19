include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "wceq.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "cr.mm"
include "wral.mm"
include "fveere.mm"
include "resubcl.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "cn.mm"
include "eleenn.mm"
include "mptelee.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "3adant1.mm"
include "eqeltrd.mm"

theorem eleesubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vi: setvar i
  let cN: class N
  assume eleesubd.1: |- ( ph -> C = ( i e. ( 1 ... N ) |-> ( ( A ` i ) - ( B ` i ) ) ) )

  disjoint N i
  disjoint A i
  disjoint B i
  assert |- ( ( ph /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> C e. ( EE ` N ) )

  proof
    wph
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    w3a
    cC
    vi
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    #
    @4
    cB
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    @0
    wph
    @1
    cC
    @8
    wceq
    @2
    eleesubd.1
    3ad2ant1
    @1
    @2
    @8
    @0
    wcel
    #
    wph
    @1
    @2
    wa
    #
    @9
    @7
    cr
    wcel
    #
    vi
    @3
    wral
    #
    @10
    @11
    vi
    @3
    @1
    @2
    @4
    @3
    wcel
    #
    @11
    @1
    @13
    wa
    @5
    cr
    wcel
    @6
    cr
    wcel
    @11
    @2
    @13
    wa
    cA
    @4
    cN
    fveere
    cB
    @4
    cN
    fveere
    @5
    @6
    resubcl
    syl2an
    anandirs
    ralrimiva
    @1
    @9
    @12
    wb
    #
    @2
    @1
    cN
    cn
    wcel
    @14
    cA
    cN
    eleenn
    @5
    @6
    vi
    cmin
    cN
    mptelee
    syl
    adantr
    mpbird
    3adant1
    eqeltrd
end
