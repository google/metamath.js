include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "cmin.mm"
include "cexp.mm"
include "ccj.mm"
include "cfv.mm"
include "cc.mm"
include "neg1cn.mm"
include "cr.mm"
include "2re.mm"
include "simpl.mm"
include "nndivre.mm"
include "sylancr.mm"
include "recnd.mm"
include "cxpcl.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "neg1ne0.mm"
include "cxpne0d.mm"
include "simpr.mm"
include "nnz.mm"
include "adantr.mm"
include "expsubd.mm"
include "wceq.mm"
include "root1id.mm"
include "oveq1d.mm"
include "cabs.mm"
include "expclzd.mm"
include "expne0d.mm"
include "recval.mm"
include "syl2anc.mm"
include "absexpz.mm"
include "syl3anc.mm"
include "abscxp2.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "1cxpd.mm"
include "eqtrd.mm"
include "1exp.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "sq1.mm"
include "oveq2d.mm"
include "cjcld.mm"
include "div1d.mm"
include "3eqtrrd.mm"

theorem root1cj
  let cK: class K
  let cN: class N


  assert |- ( ( N e. NN /\ K e. ZZ ) -> ( * ` ( ( -u 1 ^c ( 2 / N ) ) ^ K ) ) = ( ( -u 1 ^c ( 2 / N ) ) ^ ( N - K ) ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    c1
    cneg
    #
    c2
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    cN
    cK
    cmin
    co
    cexp
    co
    @5
    cN
    cexp
    co
    #
    @5
    cK
    cexp
    co
    #
    cdiv
    co
    c1
    @7
    cdiv
    co
    #
    @7
    ccj
    cfv
    #
    @2
    @5
    cN
    cK
    @2
    @3
    cc
    wcel
    #
    @4
    cc
    wcel
    @5
    cc
    wcel
    #
    neg1cn
    @2
    @4
    @2
    c2
    cr
    wcel
    @0
    @4
    cr
    wcel
    #
    2re
    @0
    @1
    simpl
    c2
    cN
    nndivre
    sylancr
    #
    recnd
    #
    @3
    @4
    cxpcl
    sylancr
    #
    @2
    @3
    @4
    @10
    @2
    neg1cn
    a1i
    @3
    cc0
    wne
    @2
    neg1ne0
    a1i
    @14
    cxpne0d
    #
    @0
    @1
    simpr
    #
    @0
    cN
    cz
    wcel
    @1
    cN
    nnz
    adantr
    expsubd
    @2
    @6
    c1
    @7
    cdiv
    @0
    @6
    c1
    wceq
    @1
    cN
    root1id
    adantr
    oveq1d
    @2
    @8
    @9
    @7
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @9
    c1
    cdiv
    co
    @9
    @2
    @7
    cc
    wcel
    @7
    cc0
    wne
    @8
    @20
    wceq
    @2
    @5
    cK
    @15
    @16
    @17
    expclzd
    #
    @2
    @5
    cK
    @15
    @16
    @17
    expne0d
    @7
    recval
    syl2anc
    @2
    @19
    c1
    @9
    cdiv
    @2
    @19
    c1
    c2
    cexp
    co
    c1
    @2
    @18
    c1
    c2
    cexp
    @2
    @18
    @5
    cabs
    cfv
    #
    cK
    cexp
    co
    #
    c1
    cK
    cexp
    co
    #
    c1
    @2
    @11
    @5
    cc0
    wne
    @1
    @18
    @23
    wceq
    @15
    @16
    @17
    @5
    cK
    absexpz
    syl3anc
    @2
    @22
    c1
    cK
    cexp
    @2
    @22
    c1
    @4
    ccxp
    co
    #
    c1
    @2
    @22
    @3
    cabs
    cfv
    #
    @4
    ccxp
    co
    #
    @25
    @2
    @10
    @12
    @22
    @27
    wceq
    neg1cn
    @13
    @3
    @4
    abscxp2
    sylancr
    @26
    c1
    @4
    ccxp
    @26
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    syl6eq
    @2
    @4
    @14
    1cxpd
    eqtrd
    oveq1d
    @1
    @24
    c1
    wceq
    @0
    cK
    1exp
    adantl
    3eqtrd
    oveq1d
    sq1
    syl6eq
    oveq2d
    @2
    @9
    @2
    @7
    @21
    cjcld
    div1d
    3eqtrd
    3eqtrrd
end
