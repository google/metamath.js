include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "csqrt.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl2an.mm"
include "abscl.mm"
include "syl.mm"
include "absge0.mm"
include "sqrtsq.mm"
include "syl2anc.mm"
include "absreimsq.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem absreim
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( abs ` ( A + ( _i x. B ) ) ) = ( sqrt ` ( ( A ^ 2 ) + ( B ^ 2 ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @5
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    #
    csqrt
    cfv
    @2
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @7
    @5
    wceq
    @2
    @4
    cc
    wcel
    #
    @9
    @0
    cA
    cc
    wcel
    @3
    cc
    wcel
    #
    @11
    @1
    cA
    recn
    @1
    ci
    cc
    wcel
    cB
    cc
    wcel
    @12
    ax-icn
    cB
    recn
    ci
    cB
    mulcl
    sylancr
    cA
    @3
    addcl
    syl2an
    #
    @4
    abscl
    syl
    @2
    @11
    @10
    @13
    @4
    absge0
    syl
    @5
    sqrtsq
    syl2anc
    @2
    @6
    @8
    csqrt
    cA
    cB
    absreimsq
    fveq2d
    eqtr3d
end
