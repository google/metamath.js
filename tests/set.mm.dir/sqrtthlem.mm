include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cv.mm"
include "crio.mm"
include "sqrtval.mm"
include "eqcomd.mm"
include "wreu.mm"
include "wb.mm"
include "sqrtcl.mm"
include "sqreu.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "neleq1.mm"
include "syl.mm"
include "3anbi123d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem sqrtthlem
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( ( ( sqrt ` A ) ^ 2 ) = A /\ 0 <_ ( Re ` ( sqrt ` A ) ) /\ ( _i x. ( sqrt ` A ) ) e/ RR+ ) )

  proof
    cA
    cc
    wcel
    #
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @1
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @1
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    wceq
    #
    cc0
    @9
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @9
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    crio
    #
    @1
    wceq
    #
    @0
    @1
    @17
    vx
    cA
    sqrtval
    eqcomd
    @0
    @1
    cc
    wcel
    @16
    vx
    cc
    wreu
    @8
    @18
    wb
    cA
    sqrtcl
    vx
    cA
    sqreu
    @16
    @8
    vx
    cc
    @1
    @9
    @1
    wceq
    #
    @11
    @3
    @13
    @5
    @15
    @7
    @19
    @10
    @2
    cA
    @9
    @1
    c2
    cexp
    oveq1
    eqeq1d
    @19
    @12
    @4
    cc0
    cle
    @9
    @1
    cre
    fveq2
    breq2d
    @19
    @14
    @6
    wceq
    @15
    @7
    wb
    @9
    @1
    ci
    cmul
    oveq2
    @14
    @6
    crp
    neleq1
    syl
    3anbi123d
    riota2
    syl2anc
    mpbird
end
