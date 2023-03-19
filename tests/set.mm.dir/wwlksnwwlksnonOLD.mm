include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "cwwlksnon.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wwlknbp2OLD.mm"
include "adantl.mm"
include "cfzo.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ad3antrrr.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "wrdsymbcl.mm"
include "syl2an2.mm"
include "fzonn0p1.mm"
include "simplr.mm"
include "eqidd.mm"
include "eqeq2.mm"
include "3anbi2d.mm"
include "3anbi3d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "mpdan.mm"
include "ex.mm"
include "wi.mm"
include "simp1.mm"
include "a1i.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "wwlknonOLD.mm"
include "bicomd.mm"
include "2rexbidva.mm"
include "bitrd.mm"

theorem wwlksnwwlksnonOLD
  let cU: class U
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
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
  disjoint U a
  disjoint U b
  disjoint G f
  disjoint a f
  disjoint b f
  disjoint N f
  disjoint V f
  disjoint W f
  disjoint U f
  assert |- ( ( N e. NN0 /\ G e. U ) -> ( W e. ( N WWalksN G ) <-> E. a e. V E. b e. V W e. ( a ( N WWalksNOn G ) b ) ) )

  proof
    cN
    cn0
    wcel
    #
    cG
    cU
    wcel
    #
    wa
    #
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    @3
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
    @5
    @8
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
    @2
    @3
    @11
    @2
    @3
    @11
    @2
    @3
    wa
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
    wa
    #
    @11
    @3
    @20
    @2
    cG
    cN
    cW
    wwlknbp2OLD
    adantl
    @13
    @20
    wa
    #
    @4
    cV
    wcel
    #
    @7
    cV
    wcel
    #
    @3
    @4
    @4
    wceq
    #
    @7
    @7
    wceq
    #
    @11
    @20
    cW
    cV
    cword
    #
    wcel
    #
    @13
    cc0
    cc0
    @17
    cfzo
    co
    #
    wcel
    #
    @22
    @16
    @27
    @19
    @16
    @27
    @15
    @26
    cW
    @14
    cV
    cV
    @14
    wwlksnwwlksnon.v
    eqcomi
    wrdeqi
    eleq2i
    biimpi
    adantr
    #
    @21
    @29
    cc0
    cc0
    @18
    cfzo
    co
    #
    wcel
    #
    @0
    @32
    @1
    @3
    @20
    @0
    @18
    cn
    wcel
    @32
    cN
    nn0p1nn
    @18
    lbfzo0
    sylibr
    ad3antrrr
    @19
    @29
    @32
    wb
    @13
    @16
    @19
    @28
    @31
    cc0
    @17
    @18
    cc0
    cfzo
    oveq2
    #
    eleq2d
    ad2antll
    mpbird
    cc0
    cV
    cW
    wrdsymbcl
    syl2an2
    @20
    @27
    @13
    cN
    @28
    wcel
    #
    @23
    @30
    @21
    @34
    cN
    @31
    wcel
    #
    @0
    @35
    @1
    @3
    @20
    cN
    fzonn0p1
    ad3antrrr
    @19
    @34
    @35
    wb
    @13
    @16
    @19
    @28
    @31
    cN
    @33
    eleq2d
    ad2antll
    mpbird
    cN
    cV
    cW
    wrdsymbcl
    syl2an2
    @2
    @3
    @20
    simplr
    @21
    @4
    eqidd
    @21
    @7
    eqidd
    @10
    @3
    @24
    @25
    w3a
    @3
    @24
    @9
    w3a
    va
    vb
    @4
    @7
    cV
    cV
    @5
    @4
    wceq
    @6
    @24
    @3
    @9
    @5
    @4
    @4
    eqeq2
    3anbi2d
    @8
    @7
    wceq
    @9
    @25
    @3
    @24
    @8
    @7
    @7
    eqeq2
    3anbi3d
    rspc2ev
    syl113anc
    mpdan
    ex
    @2
    @10
    @3
    va
    vb
    cV
    cV
    @10
    @3
    wi
    @2
    @5
    cV
    wcel
    @8
    cV
    wcel
    wa
    #
    wa
    @3
    @6
    @9
    simp1
    a1i
    rexlimdvva
    impbid
    @2
    @10
    @12
    va
    vb
    cV
    cV
    @36
    @10
    @12
    wb
    @2
    @36
    @12
    @10
    @5
    @8
    cG
    cN
    cV
    cW
    wwlksnwwlksnon.v
    wwlknonOLD
    bicomd
    adantl
    2rexbidva
    bitrd
end
