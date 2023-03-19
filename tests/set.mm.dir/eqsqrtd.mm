include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cc.mm"
include "wrmo.mm"
include "wcel.mm"
include "csqrt.mm"
include "wreu.mm"
include "sqreu.mm"
include "reurmo.mm"
include "3syl.mm"
include "wn.mm"
include "df-nel.mm"
include "sylibr.mm"
include "3jca.mm"
include "sqrtcl.mm"
include "syl.mm"
include "sqrtthlem.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "breq2d.mm"
include "wb.mm"
include "oveq2.mm"
include "neleq1.mm"
include "3anbi123d.mm"
include "rmoi.mm"
include "syl122anc.mm"

theorem eqsqrtd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume eqsqrtd.1: |- ( ph -> A e. CC )
  assume eqsqrtd.2: |- ( ph -> B e. CC )
  assume eqsqrtd.3: |- ( ph -> ( A ^ 2 ) = B )
  assume eqsqrtd.4: |- ( ph -> 0 <_ ( Re ` A ) )
  assume eqsqrtd.5: |- ( ph -> -. ( _i x. A ) e. RR+ )


  assert |- ( ph -> A = ( sqrt ` B ) )

  proof
    wph
    vx
    cv
    #
    c2
    cexp
    co
    #
    cB
    wceq
    #
    cc0
    @0
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @0
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
    wrmo
    #
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    #
    cB
    wceq
    #
    cc0
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    cA
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    cB
    csqrt
    cfv
    #
    cc
    wcel
    #
    @16
    c2
    cexp
    co
    #
    cB
    wceq
    #
    cc0
    @16
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @16
    cmul
    co
    #
    crp
    wnel
    #
    w3a
    #
    cA
    @16
    wceq
    wph
    cB
    cc
    wcel
    #
    @7
    vx
    cc
    wreu
    @8
    eqsqrtd.2
    vx
    cB
    sqreu
    @7
    vx
    cc
    reurmo
    3syl
    eqsqrtd.1
    wph
    @10
    @12
    @14
    eqsqrtd.3
    eqsqrtd.4
    wph
    @13
    crp
    wcel
    wn
    @14
    eqsqrtd.5
    @13
    crp
    df-nel
    sylibr
    3jca
    wph
    @25
    @17
    eqsqrtd.2
    cB
    sqrtcl
    syl
    wph
    @25
    @24
    eqsqrtd.2
    cB
    sqrtthlem
    syl
    @7
    @15
    @24
    vx
    cc
    cA
    @16
    @0
    cA
    wceq
    #
    @2
    @10
    @4
    @12
    @6
    @14
    @26
    @1
    @9
    cB
    @0
    cA
    c2
    cexp
    oveq1
    eqeq1d
    @26
    @3
    @11
    cc0
    cle
    @0
    cA
    cre
    fveq2
    breq2d
    @26
    @5
    @13
    wceq
    @6
    @14
    wb
    @0
    cA
    ci
    cmul
    oveq2
    @5
    @13
    crp
    neleq1
    syl
    3anbi123d
    @0
    @16
    wceq
    #
    @2
    @19
    @4
    @21
    @6
    @23
    @27
    @1
    @18
    cB
    @0
    @16
    c2
    cexp
    oveq1
    eqeq1d
    @27
    @3
    @20
    cc0
    cle
    @0
    @16
    cre
    fveq2
    breq2d
    @27
    @5
    @22
    wceq
    @6
    @23
    wb
    @0
    @16
    ci
    cmul
    oveq2
    @5
    @22
    crp
    neleq1
    syl
    3anbi123d
    rmoi
    syl122anc
end
