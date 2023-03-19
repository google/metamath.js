include "c1.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "cword.mm"
include "cc0.mm"
include "csn.mm"
include "cedg.mm"
include "w3a.mm"
include "cv.mm"
include "cs1.mm"
include "wa.mm"
include "wrex.mm"
include "clwwlkn1.mm"
include "wi.mm"
include "wrdl1exs1.mm"
include "fveq1.mm"
include "s1fv.mm"
include "sylan9eq.mm"
include "sneqd.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "com13.mm"
include "imp.mm"
include "ancld.mm"
include "reximdva.mm"
include "syl5com.mm"
include "expcom.mm"
include "3imp.mm"
include "s1len.mm"
include "a1i.mm"
include "s1cl.mm"
include "adantr.mm"
include "eqcomd.mm"
include "3jca.mm"
include "adantrl.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eleq1.mm"
include "3anbi123d.mm"
include "ad2antrl.mm"
include "mpbird.mm"
include "rexlimiva.mm"
include "impbii.mm"
include "bitri.mm"

theorem clwwlkn1loopb
  let vv: setvar v
  let cG: class G
  let cW: class W

  disjoint G v
  disjoint W v
  assert |- ( W e. ( 1 ClWWalksN G ) <-> E. v e. ( Vtx ` G ) ( W = <" v "> /\ { v } e. ( Edg ` G ) ) )

  proof
    cW
    c1
    cG
    cclwwlkn
    co
    wcel
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cc0
    cW
    cfv
    #
    csn
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    cW
    vv
    cv
    #
    cs1
    #
    wceq
    #
    @10
    csn
    #
    @7
    wcel
    #
    wa
    #
    vv
    @2
    wrex
    #
    cG
    cW
    clwwlkn1
    @9
    @16
    @1
    @4
    @8
    @16
    @4
    @1
    @8
    @16
    wi
    @4
    @1
    wa
    @12
    vv
    @2
    wrex
    @8
    @16
    @2
    cW
    vv
    wrdl1exs1
    @8
    @12
    @15
    vv
    @2
    @8
    @10
    @2
    wcel
    #
    wa
    @12
    @14
    @8
    @17
    @12
    @14
    wi
    @12
    @17
    @8
    @14
    @12
    @17
    @8
    @14
    wi
    @12
    @17
    wa
    #
    @8
    @14
    @18
    @6
    @13
    @7
    @18
    @5
    @10
    @12
    @17
    @5
    cc0
    @11
    cfv
    #
    @10
    cc0
    cW
    @11
    fveq1
    #
    @10
    @2
    s1fv
    #
    sylan9eq
    sneqd
    eleq1d
    biimpd
    ex
    com13
    imp
    ancld
    reximdva
    syl5com
    expcom
    3imp
    @15
    @9
    vv
    @2
    @17
    @15
    wa
    @9
    @11
    chash
    cfv
    #
    c1
    wceq
    #
    @11
    @3
    wcel
    #
    @19
    csn
    #
    @7
    wcel
    #
    w3a
    #
    @17
    @14
    @27
    @12
    @17
    @14
    wa
    #
    @23
    @24
    @26
    @23
    @28
    @10
    s1len
    a1i
    @17
    @24
    @14
    @10
    @2
    s1cl
    adantr
    @17
    @14
    @26
    @17
    @14
    @26
    @17
    @13
    @25
    @7
    @17
    @10
    @19
    @17
    @19
    @10
    @21
    eqcomd
    sneqd
    eleq1d
    biimpd
    imp
    3jca
    adantrl
    @12
    @9
    @27
    wb
    @17
    @14
    @12
    @1
    @23
    @4
    @24
    @8
    @26
    @12
    @0
    @22
    c1
    cW
    @11
    chash
    fveq2
    eqeq1d
    cW
    @11
    @3
    eleq1
    @12
    @6
    @25
    @7
    @12
    @5
    @19
    @20
    sneqd
    eleq1d
    3anbi123d
    ad2antrl
    mpbird
    rexlimiva
    impbii
    bitri
end
