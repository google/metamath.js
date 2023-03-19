include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "cwwlksnon.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wwlknbp1.mm"
include "wa.mm"
include "cfzo.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "adantl.mm"
include "wrdsymbcl.mm"
include "syl2an2.mm"
include "fzonn0p1.mm"
include "syl2anc.mm"
include "simpl.mm"
include "eqidd.mm"
include "eqeq2.mm"
include "3anbi2d.mm"
include "3anbi3d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "mpdan.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "impbii.mm"
include "wwlknon.mm"
include "bicomi.mm"
include "2rexbii.mm"
include "bitri.mm"

theorem wwlksnwwlksnon
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume wwlksnwwlksnon.v: |- V = ( Vtx ` G )

  disjoint G a
  disjoint G b
  disjoint a b
  disjoint N a
  disjoint N b
  disjoint V a
  disjoint V b
  disjoint W a
  disjoint W b
  assert |- ( W e. ( N WWalksN G ) <-> E. a e. V E. b e. V W e. ( a ( N WWalksNOn G ) b ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @0
    cc0
    cW
    cfv
    #
    va
    cv
    #
    wceq
    #
    cN
    cW
    cfv
    #
    vb
    cv
    #
    wceq
    #
    w3a
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    cW
    @2
    @5
    cN
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    @0
    @8
    @0
    cN
    cn0
    wcel
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
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @8
    cG
    cN
    cW
    wwlknbp1
    @0
    @17
    wa
    #
    @1
    cV
    wcel
    #
    @4
    cV
    wcel
    #
    @0
    @1
    @1
    wceq
    #
    @4
    @4
    wceq
    #
    @8
    @17
    cW
    cV
    cword
    #
    wcel
    #
    @0
    cc0
    cc0
    @14
    cfzo
    co
    #
    wcel
    #
    @19
    @13
    @10
    @24
    @16
    @13
    @24
    @12
    @23
    cW
    @11
    cV
    cV
    @11
    wwlksnwwlksnon.v
    eqcomi
    wrdeqi
    eleq2i
    biimpi
    3ad2ant2
    #
    @17
    @26
    @0
    @17
    @26
    cc0
    cc0
    @15
    cfzo
    co
    #
    wcel
    #
    @10
    @13
    @29
    @16
    @10
    @15
    cn
    wcel
    @29
    cN
    nn0p1nn
    @15
    lbfzo0
    sylibr
    3ad2ant1
    @16
    @10
    @26
    @29
    wb
    @13
    @16
    @25
    @28
    cc0
    @14
    @15
    cc0
    cfzo
    oveq2
    #
    eleq2d
    3ad2ant3
    mpbird
    adantl
    cc0
    cV
    cW
    wrdsymbcl
    syl2an2
    @17
    @20
    @0
    @17
    @24
    cN
    @25
    wcel
    #
    @20
    @27
    @17
    @31
    cN
    @28
    wcel
    #
    @10
    @13
    @32
    @16
    cN
    fzonn0p1
    3ad2ant1
    @16
    @10
    @31
    @32
    wb
    @13
    @16
    @25
    @28
    cN
    @30
    eleq2d
    3ad2ant3
    mpbird
    cN
    cV
    cW
    wrdsymbcl
    syl2anc
    adantl
    @0
    @17
    simpl
    @18
    @1
    eqidd
    @18
    @4
    eqidd
    @7
    @0
    @21
    @22
    w3a
    @0
    @21
    @6
    w3a
    va
    vb
    @1
    @4
    cV
    cV
    @2
    @1
    wceq
    @3
    @21
    @0
    @6
    @2
    @1
    @1
    eqeq2
    3anbi2d
    @5
    @4
    wceq
    @6
    @22
    @0
    @21
    @5
    @4
    @4
    eqeq2
    3anbi3d
    rspc2ev
    syl113anc
    mpdan
    @7
    @0
    va
    vb
    cV
    cV
    @7
    @0
    wi
    @2
    cV
    wcel
    @5
    cV
    wcel
    wa
    @0
    @3
    @6
    simp1
    a1i
    rexlimivv
    impbii
    @7
    @9
    va
    vb
    cV
    cV
    @9
    @7
    @2
    @5
    cG
    cN
    cW
    wwlknon
    bicomi
    2rexbii
    bitri
end
