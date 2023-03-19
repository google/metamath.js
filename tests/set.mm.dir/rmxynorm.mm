include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "crmx.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "crmy.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "simpr.mm"
include "eqidd.mm"
include "anim12i.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cn0.mm"
include "wb.mm"
include "simpl.mm"
include "frmx.mm"
include "fovcl.mm"
include "frmy.mm"
include "rmxycomplete.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem rmxynorm
  let cA: class A
  let cN: class N
  let va: setvar a


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( ( ( A rmX N ) ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( ( A rmY N ) ^ 2 ) ) ) = 1 )

  proof
    cA
    c2
    cuz
    cfv
    #
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
    crmx
    co
    #
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    cA
    cN
    crmy
    co
    #
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    @4
    cA
    va
    cv
    #
    crmx
    co
    #
    wceq
    #
    @5
    cA
    @7
    crmy
    co
    #
    wceq
    #
    wa
    #
    va
    cz
    wrex
    #
    @3
    @2
    @4
    @4
    wceq
    #
    @5
    @5
    wceq
    #
    wa
    #
    @13
    @1
    @2
    simpr
    @1
    @14
    @2
    @15
    @1
    @4
    eqidd
    @2
    @5
    eqidd
    anim12i
    @12
    @16
    va
    cN
    cz
    @7
    cN
    wceq
    #
    @9
    @14
    @11
    @15
    @17
    @8
    @4
    @4
    @7
    cN
    cA
    crmx
    oveq2
    eqeq2d
    @17
    @10
    @5
    @5
    @7
    cN
    cA
    crmy
    oveq2
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    @3
    @1
    @4
    cn0
    wcel
    @5
    cz
    wcel
    @6
    @13
    wb
    @1
    @2
    simpl
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    cA
    cN
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    cA
    va
    @4
    @5
    rmxycomplete
    syl3anc
    mpbird
end
