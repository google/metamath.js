include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cconngr.mm"
include "wi.mm"
include "cv.mm"
include "cpthson.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wral.mm"
include "snidg.mm"
include "adantr.mm"
include "wb.mm"
include "eleq2.mm"
include "ad2antll.mm"
include "mpbird.mm"
include "eqid.mm"
include "0pthonv.mm"
include "syl.mm"
include "oveq2.mm"
include "breqd.mm"
include "2exbidv.mm"
include "ralsng.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "id.mm"
include "raleq.mm"
include "raleqbidv.mm"
include "isconngr.mm"
include "ad2antrl.mm"
include "ex.mm"
include "wn.mm"
include "c0.mm"
include "snprc.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "0vconngr.mm"
include "syl6bi.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem 1conngr
  let cG: class G
  let cN: class N
  let cW: class W
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p


  assert |- ( ( G e. W /\ ( Vtx ` G ) = { N } ) -> G e. ConnGraph )

  proof
    cN
    cvv
    wcel
    #
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    cN
    csn
    #
    wceq
    #
    wa
    #
    cG
    cconngr
    wcel
    #
    wi
    #
    @0
    @5
    @6
    @0
    @5
    wa
    #
    @6
    vf
    cv
    #
    vp
    cv
    #
    vk
    cv
    #
    vn
    cv
    #
    cG
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    @2
    wral
    #
    vk
    @2
    wral
    #
    @8
    @18
    @16
    vn
    @3
    wral
    #
    vk
    @3
    wral
    #
    @8
    @20
    @9
    @10
    cN
    @12
    @13
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    @3
    wral
    #
    @8
    @24
    @9
    @10
    cN
    cN
    @13
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    @8
    cN
    @2
    wcel
    #
    @27
    @8
    @28
    cN
    @3
    wcel
    #
    @0
    @29
    @5
    cN
    cvv
    snidg
    adantr
    @4
    @28
    @29
    wb
    @0
    @1
    @2
    @3
    cN
    eleq2
    ad2antll
    mpbird
    vf
    cG
    cN
    @2
    vp
    @2
    eqid
    #
    0pthonv
    syl
    @0
    @24
    @27
    wb
    @5
    @23
    @27
    vn
    cN
    cvv
    @12
    cN
    wceq
    #
    @22
    @26
    vf
    vp
    @31
    @21
    @25
    @9
    @10
    @12
    cN
    cN
    @13
    oveq2
    breqd
    2exbidv
    ralsng
    adantr
    mpbird
    @0
    @20
    @24
    wb
    @5
    @19
    @24
    vk
    cN
    cvv
    @11
    cN
    wceq
    #
    @16
    @23
    vn
    @3
    @32
    @15
    @22
    vf
    vp
    @32
    @14
    @21
    @9
    @10
    @11
    cN
    @12
    @13
    oveq1
    breqd
    2exbidv
    ralbidv
    ralsng
    adantr
    mpbird
    @4
    @18
    @20
    wb
    @0
    @1
    @4
    @17
    @19
    vk
    @2
    @3
    @4
    id
    @16
    vn
    @2
    @3
    raleq
    raleqbidv
    ad2antll
    mpbird
    @1
    @6
    @18
    wb
    @0
    @4
    vf
    vk
    vn
    cG
    @2
    cW
    vp
    @30
    isconngr
    ad2antrl
    mpbird
    ex
    @0
    wn
    @3
    c0
    wceq
    #
    @7
    cN
    snprc
    @33
    @5
    @1
    @2
    c0
    wceq
    #
    wa
    @6
    @33
    @4
    @34
    @1
    @3
    c0
    @2
    eqeq2
    anbi2d
    cG
    cW
    0vconngr
    syl6bi
    sylbi
    pm2.61i
end
