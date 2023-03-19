include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "wral.mm"
include "wwlknbp1.mm"
include "cfzo.mm"
include "simp2.mm"
include "wa.mm"
include "cz.mm"
include "nn0z.mm"
include "fzval3.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wb.mm"
include "oveq2.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "mpbird.mm"
include "wrdsymbcl.mm"
include "syl2an2r.mm"
include "ralrimiva.mm"

theorem wwlknvtx
  let vi: setvar i
  let cG: class G
  let cN: class N
  let cW: class W

  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( W e. ( N WWalksN G ) -> A. i e. ( 0 ... N ) ( W ` i ) e. ( Vtx ` G ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
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
    vi
    cv
    #
    cW
    cfv
    @1
    wcel
    #
    vi
    cc0
    cN
    cfz
    co
    #
    wral
    cG
    cN
    cW
    wwlknbp1
    @6
    @8
    vi
    @9
    @6
    @2
    @7
    @9
    wcel
    #
    @7
    cc0
    @3
    cfzo
    co
    #
    wcel
    #
    @8
    @0
    @2
    @5
    simp2
    @6
    @10
    wa
    @12
    @7
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    @6
    @10
    @14
    @6
    @9
    @13
    @7
    @0
    @2
    @9
    @13
    wceq
    #
    @5
    @0
    cN
    cz
    wcel
    @15
    cN
    nn0z
    cc0
    cN
    fzval3
    syl
    3ad2ant1
    eleq2d
    biimpa
    @6
    @12
    @14
    wb
    #
    @10
    @5
    @0
    @16
    @2
    @5
    @11
    @13
    @7
    @3
    @4
    cc0
    cfzo
    oveq2
    eleq2d
    3ad2ant3
    adantr
    mpbird
    @7
    @1
    cW
    wrdsymbcl
    syl2an2r
    ralrimiva
    syl
end
