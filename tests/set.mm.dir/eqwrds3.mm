include "cword.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "c3.mm"
include "c1.mm"
include "c2.mm"
include "wb.mm"
include "s3cl.mm"
include "eqwrd.mm"
include "sylan2.mm"
include "s3len.mm"
include "eqeq2i.mm"
include "a1i.mm"
include "anbi1d.mm"
include "ctp.mm"
include "oveq2.mm"
include "fzo0to3tp.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "cz.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "s3fv0.mm"
include "3ad2ant1.mm"
include "eqeq2d.mm"
include "sylan9bbr.mm"
include "s3fv1.mm"
include "3ad2ant2.mm"
include "s3fv2.mm"
include "3ad2ant3.mm"
include "0zd.mm"
include "1zzd.mm"
include "2z.mm"
include "raltpd.mm"
include "adantl.mm"
include "pm5.32da.mm"
include "3bitrd.mm"

theorem eqwrds3
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word V /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( W = <" A B C "> <-> ( ( # ` W ) = 3 /\ ( ( W ` 0 ) = A /\ ( W ` 1 ) = B /\ ( W ` 2 ) = C ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cW
    cA
    cB
    cC
    cs3
    #
    wceq
    #
    cW
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    wceq
    #
    vi
    cv
    #
    cW
    cfv
    #
    @12
    @7
    cfv
    #
    wceq
    #
    vi
    cc0
    @9
    cfzo
    co
    #
    wral
    #
    wa
    #
    @9
    c3
    wceq
    #
    @17
    wa
    @19
    cc0
    cW
    cfv
    #
    cA
    wceq
    #
    c1
    cW
    cfv
    #
    cB
    wceq
    #
    c2
    cW
    cfv
    #
    cC
    wceq
    #
    w3a
    #
    wa
    @5
    @1
    @7
    @0
    wcel
    @8
    @18
    wb
    cA
    cB
    cC
    cV
    s3cl
    cW
    vi
    cV
    @7
    eqwrd
    sylan2
    @6
    @11
    @19
    @17
    @11
    @19
    wb
    @6
    @10
    c3
    @9
    cA
    cB
    cC
    s3len
    eqeq2i
    a1i
    anbi1d
    @6
    @19
    @17
    @26
    @19
    @17
    @15
    vi
    cc0
    c1
    c2
    ctp
    #
    wral
    #
    @6
    @26
    @19
    @15
    vi
    @16
    @27
    @19
    @16
    cc0
    c3
    cfzo
    co
    @27
    @9
    c3
    cc0
    cfzo
    oveq2
    fzo0to3tp
    syl6eq
    raleqdv
    @5
    @28
    @26
    wb
    @1
    @5
    @15
    @21
    @23
    @25
    vi
    cc0
    c1
    c2
    cz
    cz
    cz
    @12
    cc0
    wceq
    #
    @15
    @20
    cc0
    @7
    cfv
    #
    wceq
    @5
    @21
    @29
    @13
    @20
    @14
    @30
    @12
    cc0
    cW
    fveq2
    @12
    cc0
    @7
    fveq2
    eqeq12d
    @5
    @30
    cA
    @20
    @2
    @3
    @30
    cA
    wceq
    @4
    cA
    cB
    cC
    cV
    s3fv0
    3ad2ant1
    eqeq2d
    sylan9bbr
    @12
    c1
    wceq
    #
    @15
    @22
    c1
    @7
    cfv
    #
    wceq
    #
    @5
    @23
    @31
    @13
    @22
    @14
    @32
    @12
    c1
    cW
    fveq2
    @12
    c1
    @7
    fveq2
    eqeq12d
    @3
    @2
    @33
    @23
    wb
    @4
    @3
    @32
    cB
    @22
    cA
    cB
    cC
    cV
    s3fv1
    eqeq2d
    3ad2ant2
    sylan9bbr
    @12
    c2
    wceq
    #
    @15
    @24
    c2
    @7
    cfv
    #
    wceq
    #
    @5
    @25
    @34
    @13
    @24
    @14
    @35
    @12
    c2
    cW
    fveq2
    @12
    c2
    @7
    fveq2
    eqeq12d
    @4
    @2
    @36
    @25
    wb
    @3
    @4
    @35
    cC
    @24
    cA
    cB
    cC
    cV
    s3fv2
    eqeq2d
    3ad2ant3
    sylan9bbr
    @5
    0zd
    @5
    1zzd
    c2
    cz
    wcel
    @5
    2z
    a1i
    raltpd
    adantl
    sylan9bbr
    pm5.32da
    3bitrd
end
