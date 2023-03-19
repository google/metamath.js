include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "zsubcl.mm"
include "3adant1.mm"
include "dvds2sub.mm"
include "syld3an3.mm"
include "ancomsd.mm"
include "imp.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "nncan.mm"
include "syl2an.mm"
include "adantr.mm"
include "breqtrd.mm"
include "expr.mm"
include "caddc.mm"
include "dvds2add.mm"
include "syld3an2.mm"
include "npcan.mm"
include "impbid.mm"

theorem dvdssub2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) /\ K || ( M - N ) ) -> ( K || M <-> K || N ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cM
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    cK
    cM
    cdvds
    wbr
    #
    cK
    cN
    cdvds
    wbr
    #
    @3
    @5
    @6
    @7
    @3
    @5
    @6
    wa
    #
    wa
    cK
    cM
    @4
    cmin
    co
    #
    cN
    cdvds
    @3
    @8
    cK
    @9
    cdvds
    wbr
    #
    @3
    @6
    @5
    @10
    @0
    @1
    @2
    @4
    cz
    wcel
    #
    @6
    @5
    wa
    @10
    wi
    @1
    @2
    @11
    @0
    cM
    cN
    zsubcl
    3adant1
    #
    cK
    cM
    @4
    dvds2sub
    syld3an3
    ancomsd
    imp
    @3
    @9
    cN
    wceq
    #
    @8
    @1
    @2
    @13
    @0
    @1
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    @13
    @2
    cM
    zcn
    #
    cN
    zcn
    #
    cM
    cN
    nncan
    syl2an
    3adant1
    adantr
    breqtrd
    expr
    @3
    @5
    @7
    @6
    @3
    @5
    @7
    wa
    #
    wa
    cK
    @4
    cN
    caddc
    co
    #
    cM
    cdvds
    @3
    @18
    cK
    @19
    cdvds
    wbr
    #
    @0
    @11
    @1
    @2
    @18
    @20
    wi
    @12
    cK
    @4
    cN
    dvds2add
    syld3an2
    imp
    @3
    @19
    cM
    wceq
    #
    @18
    @1
    @2
    @21
    @0
    @1
    @14
    @15
    @21
    @2
    @16
    @17
    cM
    cN
    npcan
    syl2an
    3adant1
    adantr
    breqtrd
    expr
    impbid
end
