include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpr.mm"
include "cpw.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "pwpr.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitri.mm"
include "wi.mm"
include "fveq2.mm"
include "cc0.mm"
include "hash0.mm"
include "eqeq2i.mm"
include "eqeq1.mm"
include "wne.mm"
include "0ne2.mm"
include "eqneqall.mm"
include "mpi.mm"
include "syl6bi.mm"
include "sylbi.mm"
include "syl.mm"
include "cvv.mm"
include "c1.mm"
include "hashsng.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "1ne2.mm"
include "syl5com.mm"
include "wn.mm"
include "snprc.mm"
include "eqeq2.mm"
include "syl6eq.mm"
include "pm2.61i.mm"
include "jaoi.mm"
include "eqeq1i.mm"
include "ax-1.mm"
include "elpri.mm"
include "orim12i.mm"
include "syl11.mm"
include "syl5bi.mm"
include "imp.mm"

theorem hash2pwpr
  let cP: class P
  let cX: class X
  let cY: class Y


  assert |- ( ( ( # ` P ) = 2 /\ P e. ~P { X , Y } ) -> P = { X , Y } )

  proof
    cP
    chash
    cfv
    #
    c2
    wceq
    #
    cP
    cX
    cY
    cpr
    #
    cpw
    #
    wcel
    #
    cP
    @2
    wceq
    #
    @4
    cP
    c0
    cX
    csn
    #
    cpr
    #
    wcel
    #
    cP
    cY
    csn
    #
    @2
    cpr
    #
    wcel
    #
    wo
    #
    @1
    @5
    @4
    cP
    @7
    @10
    cun
    #
    wcel
    @12
    @3
    @13
    cP
    cX
    cY
    pwpr
    eleq2i
    cP
    @7
    @10
    elun
    bitri
    cP
    c0
    wceq
    #
    cP
    @6
    wceq
    #
    wo
    #
    cP
    @9
    wceq
    #
    @5
    wo
    #
    wo
    @1
    @5
    @12
    @16
    @1
    @5
    wi
    #
    @18
    @14
    @19
    @15
    @14
    @0
    c0
    chash
    cfv
    #
    wceq
    #
    @19
    cP
    c0
    chash
    fveq2
    #
    @21
    @0
    cc0
    wceq
    #
    @19
    @20
    cc0
    @0
    hash0
    eqeq2i
    @23
    @1
    cc0
    c2
    wceq
    #
    @5
    @0
    cc0
    c2
    eqeq1
    @24
    cc0
    c2
    wne
    @5
    0ne2
    @5
    cc0
    c2
    eqneqall
    mpi
    #
    syl6bi
    sylbi
    syl
    cX
    cvv
    wcel
    #
    @15
    @19
    wi
    #
    @26
    @6
    chash
    cfv
    #
    c1
    wceq
    #
    @15
    @19
    cX
    cvv
    hashsng
    @15
    @29
    @0
    c1
    wceq
    #
    @19
    @15
    @28
    @0
    c1
    @28
    @0
    wceq
    @6
    cP
    @6
    cP
    chash
    fveq2
    eqcoms
    eqeq1d
    @30
    @1
    c1
    c2
    wceq
    #
    @5
    @0
    c1
    c2
    eqeq1
    @31
    c1
    c2
    wne
    @5
    1ne2
    @5
    c1
    c2
    eqneqall
    mpi
    syl6bi
    #
    syl6bi
    syl5com
    @26
    wn
    @6
    c0
    wceq
    #
    @27
    cX
    snprc
    @33
    @15
    @14
    @19
    @6
    c0
    cP
    eqeq2
    @14
    @1
    @24
    @5
    @14
    @0
    cc0
    c2
    @14
    @0
    @20
    cc0
    @22
    hash0
    syl6eq
    eqeq1d
    @25
    syl6bi
    syl6bi
    sylbi
    pm2.61i
    jaoi
    @17
    @19
    @5
    cY
    cvv
    wcel
    #
    @17
    @19
    wi
    #
    @34
    @9
    chash
    cfv
    #
    c1
    wceq
    #
    @17
    @19
    cY
    cvv
    hashsng
    @17
    @37
    @30
    @19
    @17
    @36
    @0
    c1
    @36
    @0
    wceq
    @9
    cP
    @9
    cP
    chash
    fveq2
    eqcoms
    eqeq1d
    @32
    syl6bi
    syl5com
    @34
    wn
    @9
    c0
    wceq
    #
    @35
    cY
    snprc
    @38
    @17
    @14
    @19
    @9
    c0
    cP
    eqeq2
    @14
    @1
    @20
    c2
    wceq
    #
    @5
    @14
    @0
    @20
    c2
    @22
    eqeq1d
    @39
    @24
    @5
    @20
    cc0
    c2
    hash0
    eqeq1i
    @25
    sylbi
    syl6bi
    syl6bi
    sylbi
    pm2.61i
    @5
    @1
    ax-1
    jaoi
    jaoi
    @8
    @16
    @11
    @18
    cP
    c0
    @6
    elpri
    cP
    @9
    @2
    elpri
    orim12i
    syl11
    syl5bi
    imp
end
