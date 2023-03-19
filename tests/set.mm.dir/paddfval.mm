include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "cv.mm"
include "cun.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "elex.mm"
include "cpadd.mm"
include "cfv.mm"
include "catm.mm"
include "cjn.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "eqidd.mm"
include "oveqd.mm"
include "breq123d.mm"
include "2rexbidv.mm"
include "rabeqbidv.mm"
include "uneq2d.mm"
include "mpt2eq123dv.mm"
include "df-padd.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem paddfval
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vm: setvar m
  let vn: setvar n
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vh: setvar h
  let vs: setvar s
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint m q
  disjoint m r
  disjoint K m
  disjoint n q
  disjoint n r
  disjoint K n
  disjoint p q
  disjoint p r
  disjoint K p
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint h m
  disjoint h n
  disjoint h p
  disjoint h s
  disjoint A h
  disjoint m s
  disjoint n s
  disjoint p s
  disjoint A s
  disjoint .\/ h
  disjoint h q
  disjoint h r
  disjoint K h
  disjoint q s
  disjoint r s
  disjoint K s
  disjoint .<_ h
  assert |- ( K e. B -> .+ = ( m e. ~P A , n e. ~P A |-> ( ( m u. n ) u. { p e. A | E. q e. m E. r e. n p .<_ ( q .\/ r ) } ) ) )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    c.pl
    vm
    vn
    cA
    cpw
    #
    @1
    vm
    cv
    #
    vn
    cv
    #
    cun
    #
    vp
    cv
    #
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    @3
    wrex
    vq
    @2
    wrex
    #
    vp
    cA
    crab
    #
    cun
    #
    cmpt2
    #
    wceq
    cK
    cB
    elex
    @0
    c.pl
    cK
    cpadd
    cfv
    @13
    paddfval.p
    vh
    cK
    vm
    vn
    vh
    cv
    #
    catm
    cfv
    #
    cpw
    #
    @16
    @4
    @5
    @6
    @7
    @14
    cjn
    cfv
    #
    co
    #
    @14
    cple
    cfv
    #
    wbr
    #
    vr
    @3
    wrex
    vq
    @2
    wrex
    #
    vp
    @15
    crab
    #
    cun
    #
    cmpt2
    @13
    cvv
    cpadd
    @14
    cK
    wceq
    #
    vm
    vn
    @16
    @16
    @23
    @1
    @1
    @12
    @24
    @15
    cA
    @24
    @15
    cK
    catm
    cfv
    #
    cA
    @14
    cK
    catm
    fveq2
    paddfval.a
    syl6eqr
    #
    pweqd
    #
    @27
    @24
    @22
    @11
    @4
    @24
    @21
    @10
    vp
    @15
    cA
    @26
    @24
    @20
    @9
    vq
    vr
    @2
    @3
    @24
    @5
    @5
    @18
    @8
    @19
    c.le
    @24
    @5
    eqidd
    @24
    @19
    cK
    cple
    cfv
    c.le
    @14
    cK
    cple
    fveq2
    paddfval.l
    syl6eqr
    @24
    @17
    c.or
    @6
    @7
    @24
    @17
    cK
    cjn
    cfv
    c.or
    @14
    cK
    cjn
    fveq2
    paddfval.j
    syl6eqr
    oveqd
    breq123d
    2rexbidv
    rabeqbidv
    uneq2d
    mpt2eq123dv
    vm
    vn
    vr
    vq
    vp
    vh
    df-padd
    vm
    vn
    @1
    @1
    @12
    cA
    cA
    @25
    cvv
    paddfval.a
    cK
    catm
    fvex
    eqeltri
    pwex
    #
    @28
    mpt2ex
    fvmpt
    syl5eq
    syl
end
