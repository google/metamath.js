include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cre.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cv.mm"
include "cc.mm"
include "crio.mm"
include "recn.mm"
include "sqrtval.mm"
include "eqcomd.mm"
include "syl.mm"
include "adantr.mm"
include "wreu.mm"
include "wb.mm"
include "resqrtcl.mm"
include "recnd.mm"
include "resqreu.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "neleq1.mm"
include "3anbi123d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem resqrtthlem
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( ( ( sqrt ` A ) ^ 2 ) = A /\ 0 <_ ( Re ` ( sqrt ` A ) ) /\ ( _i x. ( sqrt ` A ) ) e/ RR+ ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
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
    @3
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @3
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
    @11
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @11
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
    @3
    wceq
    #
    @0
    @20
    @1
    @0
    cA
    cc
    wcel
    #
    @20
    cA
    recn
    @21
    @3
    @19
    vx
    cA
    sqrtval
    eqcomd
    syl
    adantr
    @2
    @3
    cc
    wcel
    @18
    vx
    cc
    wreu
    @10
    @20
    wb
    @2
    @3
    cA
    resqrtcl
    recnd
    vx
    cA
    resqreu
    @18
    @10
    vx
    cc
    @3
    @11
    @3
    wceq
    #
    @13
    @5
    @15
    @7
    @17
    @9
    @22
    @12
    @4
    cA
    @11
    @3
    c2
    cexp
    oveq1
    eqeq1d
    @22
    @14
    @6
    cc0
    cle
    @11
    @3
    cre
    fveq2
    breq2d
    @22
    @16
    @8
    wceq
    @17
    @9
    wb
    @11
    @3
    ci
    cmul
    oveq2
    @16
    @8
    crp
    neleq1
    syl
    3anbi123d
    riota2
    syl2anc
    mpbird
end
