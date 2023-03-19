include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cabs.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "c1.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "efival.mm"
include "syl.mm"
include "fveq2d.mm"
include "c2.mm"
include "cexp.mm"
include "csqrt.mm"
include "recoscl.mm"
include "resincl.mm"
include "absreim.mm"
include "syl2anc.mm"
include "resqcld.mm"
include "recnd.mm"
include "addcomd.mm"
include "sincossq.mm"
include "eqtrd.mm"
include "sqrt1.mm"
include "syl6eq.mm"

theorem absefi
  let cA: class A


  assert |- ( A e. RR -> ( abs ` ( exp ` ( _i x. A ) ) ) = 1 )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    ce
    cfv
    #
    cabs
    cfv
    cA
    ccos
    cfv
    #
    ci
    cA
    csin
    cfv
    #
    cmul
    co
    caddc
    co
    #
    cabs
    cfv
    #
    c1
    @0
    @1
    @4
    cabs
    @0
    cA
    cc
    wcel
    #
    @1
    @4
    wceq
    cA
    recn
    #
    cA
    efival
    syl
    fveq2d
    @0
    @5
    @2
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    c1
    @0
    @2
    cr
    wcel
    @3
    cr
    wcel
    @5
    @11
    wceq
    cA
    recoscl
    #
    cA
    resincl
    #
    @2
    @3
    absreim
    syl2anc
    @0
    @11
    c1
    csqrt
    cfv
    c1
    @0
    @10
    c1
    csqrt
    @0
    @10
    @9
    @8
    caddc
    co
    #
    c1
    @0
    @8
    @9
    @0
    @8
    @0
    @2
    @12
    resqcld
    recnd
    @0
    @9
    @0
    @3
    @13
    resqcld
    recnd
    addcomd
    @0
    @6
    @14
    c1
    wceq
    @7
    cA
    sincossq
    syl
    eqtrd
    fveq2d
    sqrt1
    syl6eq
    eqtrd
    eqtrd
end
