include "cv.mm"
include "c1.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "c2.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "2wlkdlem3.mm"
include "wb.mm"
include "simpl.mm"
include "simpr.mm"
include "neeq12d.mm"
include "bicomd.mm"
include "3adant3.mm"
include "biimpcd.mm"
include "adantr.mm"
include "imp.mm"
include "a1d.mm"
include "eqid.mm"
include "eqneqall.mm"
include "mp1i.mm"
include "necom.mm"
include "syl6rbb.mm"
include "3adant1.mm"
include "adantl.mm"
include "3jca.mm"
include "syl2anc.mm"
include "ctp.mm"
include "c3.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0to3tp.mm"
include "raleqi.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "neeq1.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "raltp.mm"
include "bitri.mm"
include "sylibr.mm"
include "csn.mm"
include "cs2.mm"
include "s2len.mm"
include "fzo12sn.mm"
include "neeq2.mm"
include "neeq2d.mm"
include "ralsn.mm"
include "ralbii.mm"

theorem 2pthdlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )

  disjoint F k
  disjoint P k
  disjoint V k
  disjoint F j
  disjoint j k
  disjoint P j
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ ( # ` F ) ) ( k =/= j -> ( P ` k ) =/= ( P ` j ) ) )

  proof
    wph
    vk
    cv
    #
    c1
    wne
    #
    @0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wne
    #
    wi
    #
    vk
    cc0
    cP
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @0
    vj
    cv
    #
    wne
    #
    @2
    @9
    cP
    cfv
    #
    wne
    #
    wi
    #
    vj
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    vk
    @7
    wral
    wph
    cc0
    c1
    wne
    #
    cc0
    cP
    cfv
    #
    @3
    wne
    #
    wi
    #
    c1
    c1
    wne
    #
    @3
    @3
    wne
    #
    wi
    #
    c2
    c1
    wne
    #
    c2
    cP
    cfv
    #
    @3
    wne
    #
    wi
    #
    w3a
    #
    @8
    wph
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    @18
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    @25
    cC
    wceq
    #
    w3a
    #
    @28
    2wlkd.n
    wph
    cA
    cB
    cC
    cP
    cF
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkdlem3
    @31
    @35
    wa
    #
    @20
    @23
    @27
    @36
    @19
    @17
    @31
    @35
    @19
    @29
    @35
    @19
    wi
    @30
    @35
    @29
    @19
    @32
    @33
    @29
    @19
    wb
    @34
    @32
    @33
    wa
    #
    @19
    @29
    @37
    @18
    cA
    @3
    cB
    @32
    @33
    simpl
    @32
    @33
    simpr
    neeq12d
    bicomd
    3adant3
    biimpcd
    adantr
    imp
    a1d
    c1
    c1
    wceq
    @23
    @36
    c1
    eqid
    @22
    c1
    c1
    eqneqall
    mp1i
    @36
    @26
    @24
    @31
    @35
    @26
    @30
    @35
    @26
    wi
    @29
    @35
    @30
    @26
    @33
    @34
    @30
    @26
    wb
    @32
    @33
    @34
    wa
    #
    @26
    cC
    cB
    wne
    @30
    @38
    @25
    cC
    @3
    cB
    @33
    @34
    simpr
    @33
    @34
    simpl
    neeq12d
    cC
    cB
    necom
    syl6rbb
    3adant1
    biimpcd
    adantl
    imp
    a1d
    3jca
    syl2anc
    @8
    @5
    vk
    cc0
    c1
    c2
    ctp
    #
    wral
    @28
    @5
    vk
    @7
    @39
    @7
    cc0
    c3
    cfzo
    co
    @39
    @6
    c3
    cc0
    cfzo
    @6
    cA
    cB
    cC
    cs3
    #
    chash
    cfv
    c3
    cP
    @40
    chash
    2wlkd.p
    fveq2i
    cA
    cB
    cC
    s3len
    eqtri
    oveq2i
    fzo0to3tp
    eqtri
    raleqi
    @5
    @20
    @23
    @27
    vk
    cc0
    c1
    c2
    c0ex
    1ex
    2ex
    @0
    cc0
    wceq
    #
    @1
    @17
    @4
    @19
    @0
    cc0
    c1
    neeq1
    @41
    @2
    @18
    @3
    @0
    cc0
    cP
    fveq2
    neeq1d
    imbi12d
    @0
    c1
    wceq
    #
    @1
    @21
    @4
    @22
    @0
    c1
    c1
    neeq1
    @42
    @2
    @3
    @3
    @0
    c1
    cP
    fveq2
    neeq1d
    imbi12d
    @0
    c2
    wceq
    #
    @1
    @24
    @4
    @26
    @0
    c2
    c1
    neeq1
    @43
    @2
    @25
    @3
    @0
    c2
    cP
    fveq2
    neeq1d
    imbi12d
    raltp
    bitri
    sylibr
    @16
    @5
    vk
    @7
    @16
    @13
    vj
    c1
    csn
    #
    wral
    @5
    @13
    vj
    @15
    @44
    @15
    c1
    c2
    cfzo
    co
    @44
    @14
    c2
    c1
    cfzo
    @14
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @45
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    oveq2i
    fzo12sn
    eqtri
    raleqi
    @13
    @5
    vj
    c1
    1ex
    @9
    c1
    wceq
    #
    @10
    @1
    @12
    @4
    @9
    c1
    @0
    neeq2
    @46
    @11
    @3
    @2
    @9
    c1
    cP
    fveq2
    neeq2d
    imbi12d
    ralsn
    bitri
    ralbii
    sylibr
end
