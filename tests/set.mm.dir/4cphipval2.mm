include "ccph.mm"
include "wcel.mm"
include "ci.mm"
include "wa.mm"
include "w3a.mm"
include "c4.mm"
include "co.mm"
include "cmul.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "caddc.mm"
include "cdiv.mm"
include "cphipval2.mm"
include "oveq2d.mm"
include "cc.mm"
include "wss.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cphsubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simp1l.mm"
include "cgrp.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngpgrp.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "cphnmcl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "sqcld.mm"
include "grpsubcl.mm"
include "subcld.mm"
include "ax-icn.mm"
include "a1i.mm"
include "simp2.mm"
include "clmod.mm"
include "cphlmod.mm"
include "simp1r.mm"
include "simp3.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "mulcld.mm"
include "addcld.mm"
include "4cn.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "divcan2d.mm"
include "eqtrd.mm"

theorem 4cphipval2
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cW: class W
  let cX: class X
  let vk: setvar k
  assume cphipfval.x: |- X = ( Base ` W )
  assume cphipfval.p: |- .+ = ( +g ` W )
  assume cphipfval.s: |- .x. = ( .s ` W )
  assume cphipfval.n: |- N = ( norm ` W )
  assume cphipfval.i: |- ., = ( .i ` W )
  assume cphipval2.m: |- .- = ( -g ` W )
  assume cphipval2.f: |- F = ( Scalar ` W )
  assume cphipval2.k: |- K = ( Base ` F )


  assert |- ( ( ( W e. CPreHil /\ _i e. K ) /\ A e. X /\ B e. X ) -> ( 4 x. ( A ., B ) ) = ( ( ( ( N ` ( A .+ B ) ) ^ 2 ) - ( ( N ` ( A .- B ) ) ^ 2 ) ) + ( _i x. ( ( ( N ` ( A .+ ( _i .x. B ) ) ) ^ 2 ) - ( ( N ` ( A .- ( _i .x. B ) ) ) ^ 2 ) ) ) ) )

  proof
    cW
    ccph
    wcel
    #
    ci
    cK
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    c4
    cA
    cB
    c.xi
    co
    #
    cmul
    co
    c4
    cA
    cB
    c.pl
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cB
    c.mi
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
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
    c2
    cexp
    co
    #
    cA
    @14
    c.mi
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    cmul
    co
    @23
    @5
    @6
    @24
    c4
    cmul
    cA
    cB
    c.pl
    c.x
    cF
    c.xi
    cK
    c.mi
    cN
    cW
    cX
    cphipfval.x
    cphipfval.p
    cphipfval.s
    cphipfval.n
    cphipfval.i
    cphipval2.m
    cphipval2.f
    cphipval2.k
    cphipval2
    oveq2d
    @5
    @23
    c4
    @5
    @13
    @22
    @5
    @9
    @12
    @5
    @8
    @5
    cK
    cc
    @8
    @2
    @3
    cK
    cc
    wss
    #
    @4
    @0
    @25
    @1
    @0
    cK
    ccnfld
    csubrg
    cfv
    wcel
    @25
    cF
    cK
    cW
    cphipval2.f
    cphipval2.k
    cphsubrg
    cK
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    adantr
    3ad2ant1
    #
    @5
    @0
    @7
    cX
    wcel
    #
    @8
    cK
    wcel
    @0
    @1
    @3
    @4
    simp1l
    #
    @2
    cW
    cgrp
    wcel
    #
    @3
    @4
    @27
    @0
    @29
    @1
    @0
    cW
    cngp
    wcel
    @29
    cW
    cphngp
    cW
    ngpgrp
    syl
    #
    adantr
    #
    cX
    c.pl
    cW
    cA
    cB
    cphipfval.x
    cphipfval.p
    grpcl
    syl3an1
    @7
    cF
    c.xi
    cK
    cN
    cX
    cW
    cphipfval.x
    cphipfval.i
    cphipfval.n
    cphipval2.f
    cphipval2.k
    cphnmcl
    syl2anc
    sseldd
    sqcld
    @5
    @11
    @5
    cK
    cc
    @11
    @26
    @5
    @0
    @10
    cX
    wcel
    #
    @11
    cK
    wcel
    @28
    @2
    @29
    @3
    @4
    @32
    @31
    cX
    cW
    c.mi
    cA
    cB
    cphipfval.x
    cphipval2.m
    grpsubcl
    syl3an1
    @10
    cF
    c.xi
    cK
    cN
    cX
    cW
    cphipfval.x
    cphipfval.i
    cphipfval.n
    cphipval2.f
    cphipval2.k
    cphnmcl
    syl2anc
    sseldd
    sqcld
    subcld
    @5
    ci
    @21
    ci
    cc
    wcel
    @5
    ax-icn
    a1i
    @5
    @17
    @20
    @5
    @16
    @5
    cK
    cc
    @16
    @26
    @5
    @0
    @15
    cX
    wcel
    #
    @16
    cK
    wcel
    @28
    @5
    @29
    @3
    @14
    cX
    wcel
    #
    @33
    @5
    @0
    @29
    @28
    @30
    syl
    #
    @2
    @3
    @4
    simp2
    #
    @5
    cW
    clmod
    wcel
    #
    @1
    @4
    @34
    @2
    @3
    @37
    @4
    @0
    @37
    @1
    cW
    cphlmod
    adantr
    3ad2ant1
    @0
    @1
    @3
    @4
    simp1r
    @2
    @3
    @4
    simp3
    ci
    c.x
    cF
    cK
    cX
    cW
    cB
    cphipfval.x
    cphipval2.f
    cphipfval.s
    cphipval2.k
    lmodvscl
    syl3anc
    #
    cX
    c.pl
    cW
    cA
    @14
    cphipfval.x
    cphipfval.p
    grpcl
    syl3anc
    @15
    cF
    c.xi
    cK
    cN
    cX
    cW
    cphipfval.x
    cphipfval.i
    cphipfval.n
    cphipval2.f
    cphipval2.k
    cphnmcl
    syl2anc
    sseldd
    sqcld
    @5
    @19
    @5
    cK
    cc
    @19
    @26
    @5
    @0
    @18
    cX
    wcel
    #
    @19
    cK
    wcel
    @28
    @5
    @29
    @3
    @34
    @39
    @35
    @36
    @38
    cX
    cW
    c.mi
    cA
    @14
    cphipfval.x
    cphipval2.m
    grpsubcl
    syl3anc
    @18
    cF
    c.xi
    cK
    cN
    cX
    cW
    cphipfval.x
    cphipfval.i
    cphipfval.n
    cphipval2.f
    cphipval2.k
    cphnmcl
    syl2anc
    sseldd
    sqcld
    subcld
    mulcld
    addcld
    c4
    cc
    wcel
    @5
    4cn
    a1i
    c4
    cc0
    wne
    @5
    4ne0
    a1i
    divcan2d
    eqtrd
end
