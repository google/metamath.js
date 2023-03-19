include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "w3a.mm"
include "c1.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "cneg.mm"
include "cngp.mm"
include "cr.mm"
include "elin.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmngp.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "cgrp.mm"
include "clmod.mm"
include "nvclmod.mm"
include "lmodgrp.mm"
include "simp2l.mm"
include "cclm.mm"
include "id.mm"
include "cvsclm.mm"
include "simplbiim.mm"
include "simp3.mm"
include "simp2r.mm"
include "clmvscl.mm"
include "syl3anc.mm"
include "grpcl.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cabs.mm"
include "ax-icn.mm"
include "absnegi.mm"
include "absi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "wceq.mm"
include "simp1.mm"
include "wi.mm"
include "cminusg.mm"
include "clmneg.mm"
include "sylan.mm"
include "clmfgrp.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "eqeltrd.mm"
include "ex.mm"
include "imp.mm"
include "3adant2.mm"
include "ncvsprp.mm"
include "clmvsdi.mm"
include "syl13anc.mm"
include "mulneg1i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "clmvsass.mm"
include "simpr.mm"
include "anim12i.mm"
include "3adant3.mm"
include "clmvs1.mm"
include "3eqtr3a.mm"
include "oveq2d.mm"
include "cabl.mm"
include "clmabl.mm"
include "ablcom.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "syl5eqr.mm"

theorem ncvspi
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  assume ncvsprp.v: |- V = ( Base ` W )
  assume ncvsprp.n: |- N = ( norm ` W )
  assume ncvsprp.s: |- .x. = ( .s ` W )
  assume ncvsdif.p: |- .+ = ( +g ` W )
  assume ncvspi.f: |- F = ( Scalar ` W )
  assume ncvspi.k: |- K = ( Base ` F )


  assert |- ( ( W e. ( NrmVec i^i CVec ) /\ ( A e. V /\ B e. V ) /\ _i e. K ) -> ( N ` ( A .+ ( _i .x. B ) ) ) = ( N ` ( B .+ ( -u _i .x. A ) ) ) )

  proof
    cW
    cnvc
    ccvs
    cin
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
    wa
    #
    ci
    cK
    wcel
    #
    w3a
    #
    c1
    cA
    ci
    cB
    c.x
    co
    #
    c.pl
    co
    #
    cN
    cfv
    #
    cmul
    co
    #
    @8
    cB
    ci
    cneg
    #
    cA
    c.x
    co
    #
    c.pl
    co
    #
    cN
    cfv
    #
    @5
    @8
    @5
    @8
    @5
    cW
    cngp
    wcel
    #
    @7
    cV
    wcel
    #
    @8
    cr
    wcel
    @0
    @3
    @14
    @4
    @0
    cW
    cnvc
    wcel
    #
    cW
    ccvs
    wcel
    #
    wa
    #
    @14
    cW
    cnvc
    ccvs
    elin
    #
    @16
    @14
    @17
    @16
    cW
    cnlm
    wcel
    @14
    cW
    nvcnlm
    cW
    nlmngp
    syl
    adantr
    sylbi
    3ad2ant1
    @5
    cW
    cgrp
    wcel
    #
    @1
    @6
    cV
    wcel
    #
    @15
    @0
    @3
    @20
    @4
    @0
    @18
    @20
    @19
    @16
    @20
    @17
    @16
    cW
    clmod
    wcel
    @20
    cW
    nvclmod
    cW
    lmodgrp
    syl
    adantr
    sylbi
    3ad2ant1
    @0
    @1
    @2
    @4
    simp2l
    #
    @5
    cW
    cclm
    wcel
    #
    @4
    @2
    @21
    @0
    @3
    @23
    @4
    @0
    @16
    @17
    @23
    @19
    @17
    cW
    @17
    id
    cvsclm
    #
    simplbiim
    #
    3ad2ant1
    #
    @0
    @3
    @4
    simp3
    #
    @0
    @1
    @2
    @4
    simp2r
    #
    ci
    c.x
    cF
    cK
    cV
    cW
    cB
    ncvsprp.v
    ncvspi.f
    ncvsprp.s
    ncvspi.k
    clmvscl
    syl3anc
    #
    cV
    c.pl
    cW
    cA
    @6
    ncvsprp.v
    ncvsdif.p
    grpcl
    syl3anc
    #
    @7
    cW
    cN
    cV
    ncvsprp.v
    ncvsprp.n
    nmcl
    syl2anc
    recnd
    mulid2d
    @5
    @9
    @10
    cabs
    cfv
    #
    @8
    cmul
    co
    #
    @13
    @31
    c1
    @8
    cmul
    @31
    ci
    cabs
    cfv
    c1
    ci
    ax-icn
    absnegi
    absi
    eqtri
    oveq1i
    @5
    @10
    @7
    c.x
    co
    #
    cN
    cfv
    #
    @32
    @13
    @5
    @0
    @10
    cK
    wcel
    #
    @15
    @34
    @32
    wceq
    @0
    @3
    @4
    simp1
    @0
    @4
    @35
    @3
    @0
    @4
    @35
    @0
    @16
    @17
    @4
    @35
    wi
    @19
    @17
    @4
    @35
    @17
    @4
    wa
    @10
    ci
    cF
    cminusg
    cfv
    #
    cfv
    #
    cK
    @17
    @23
    @4
    @10
    @37
    wceq
    @24
    ci
    cF
    cK
    cW
    ncvspi.f
    ncvspi.k
    clmneg
    sylan
    @17
    cF
    cgrp
    wcel
    #
    @4
    @37
    cK
    wcel
    @17
    @23
    @38
    @24
    cF
    cW
    ncvspi.f
    clmfgrp
    syl
    cK
    cF
    @36
    ci
    ncvspi.k
    @36
    eqid
    grpinvcl
    sylan
    eqeltrd
    ex
    simplbiim
    imp
    3adant2
    #
    @30
    @10
    @7
    c.x
    cF
    cK
    cN
    cV
    cW
    ncvsprp.v
    ncvsprp.n
    ncvsprp.s
    ncvspi.f
    ncvspi.k
    ncvsprp
    syl3anc
    @5
    @33
    @12
    cN
    @5
    @33
    @11
    @10
    @6
    c.x
    co
    #
    c.pl
    co
    #
    @11
    cB
    c.pl
    co
    #
    @12
    @5
    @23
    @35
    @1
    @21
    @33
    @41
    wceq
    @26
    @39
    @22
    @29
    @10
    c.pl
    c.x
    cF
    cK
    cV
    cW
    cA
    @6
    ncvsprp.v
    ncvspi.f
    ncvsprp.s
    ncvspi.k
    ncvsdif.p
    clmvsdi
    syl13anc
    @5
    @40
    cB
    @11
    c.pl
    @5
    @10
    ci
    cmul
    co
    #
    cB
    c.x
    co
    #
    c1
    cB
    c.x
    co
    #
    @40
    cB
    @43
    c1
    cB
    c.x
    @43
    ci
    ci
    cmul
    co
    #
    cneg
    #
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @47
    c1
    cneg
    #
    cneg
    c1
    @46
    @48
    ixi
    negeqi
    negneg1e1
    eqtri
    eqtri
    oveq1i
    @5
    @23
    @35
    @4
    @2
    @44
    @40
    wceq
    @26
    @39
    @27
    @28
    @10
    ci
    c.x
    cF
    cK
    cV
    cW
    cB
    ncvsprp.v
    ncvspi.f
    ncvsprp.s
    ncvspi.k
    clmvsass
    syl13anc
    @5
    @23
    @2
    wa
    #
    @45
    cB
    wceq
    @0
    @3
    @49
    @4
    @0
    @23
    @3
    @2
    @25
    @1
    @2
    simpr
    anim12i
    3adant3
    c.x
    cV
    cW
    cB
    ncvsprp.v
    ncvsprp.s
    clmvs1
    syl
    3eqtr3a
    oveq2d
    @5
    cW
    cabl
    wcel
    #
    @11
    cV
    wcel
    #
    @2
    @42
    @12
    wceq
    @0
    @3
    @50
    @4
    @0
    @16
    @17
    @50
    @19
    @17
    @23
    @50
    @24
    cW
    clmabl
    syl
    simplbiim
    3ad2ant1
    @5
    @23
    @35
    @1
    @51
    @26
    @39
    @22
    @10
    c.x
    cF
    cK
    cV
    cW
    cA
    ncvsprp.v
    ncvspi.f
    ncvsprp.s
    ncvspi.k
    clmvscl
    syl3anc
    @28
    cV
    c.pl
    cW
    @11
    cB
    ncvsprp.v
    ncvsdif.p
    ablcom
    syl3anc
    3eqtrd
    fveq2d
    eqtr3d
    syl5eqr
    eqtr3d
end
