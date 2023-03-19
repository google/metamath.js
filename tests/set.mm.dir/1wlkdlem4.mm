include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cs1.mm"
include "fveq1i.mm"
include "cvv.mm"
include "wcel.mm"
include "1wlkdlem2.mm"
include "elfvexd.mm"
include "s1fv.mm"
include "syl.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "sylan2br.mm"
include "sseqtr4d.mm"
include "ifpimpda.mm"
include "wb.mm"
include "cs2.mm"
include "s2fv0.mm"
include "s2fv1.mm"
include "eqeq12.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "preq12.mm"
include "sseq1d.mm"
include "ifpbi123d.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "c0ex.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "wkslem2.mm"
include "mpdan.mm"
include "ralsn.mm"
include "sylibr.mm"
include "fveq2i.mm"
include "s1len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo01.mm"
include "a1i.mm"
include "raleqdv.mm"

theorem 1wlkdlem4
  let wph: wff ph
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )

  disjoint F k
  disjoint I k
  disjoint P k
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) )

  proof
    wph
    vk
    cv
    #
    cP
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    @0
    cF
    cfv
    cI
    cfv
    #
    @1
    csn
    wceq
    @1
    @3
    cpr
    @4
    wss
    wif
    #
    vk
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    @5
    vk
    cc0
    csn
    #
    wral
    #
    wph
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wceq
    #
    cc0
    cF
    cfv
    #
    cI
    cfv
    #
    @10
    csn
    #
    wceq
    #
    @10
    @11
    cpr
    #
    @14
    wss
    #
    wif
    #
    @9
    wph
    @19
    cX
    cY
    wceq
    #
    @14
    cX
    csn
    #
    wceq
    #
    cX
    cY
    cpr
    #
    @14
    wss
    #
    wif
    #
    wph
    @20
    @22
    @24
    wph
    @20
    wa
    @14
    cJ
    cI
    cfv
    #
    @21
    wph
    @14
    @26
    wceq
    #
    @20
    wph
    @13
    cJ
    cI
    wph
    @13
    cc0
    cJ
    cs1
    #
    cfv
    #
    cJ
    cc0
    cF
    @28
    1wlkd.f
    fveq1i
    wph
    cJ
    cvv
    wcel
    @29
    cJ
    wceq
    wph
    cX
    cI
    cJ
    wph
    cP
    cF
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkdlem2
    elfvexd
    cJ
    cvv
    s1fv
    syl
    syl5eq
    fveq2d
    #
    adantr
    1wlkd.l
    eqtrd
    wph
    @20
    wn
    #
    wa
    @23
    @26
    @14
    @31
    wph
    cX
    cY
    wne
    @23
    @26
    wss
    cX
    cY
    df-ne
    1wlkd.j
    sylan2br
    wph
    @27
    @31
    @30
    adantr
    sseqtr4d
    ifpimpda
    wph
    @10
    cX
    wceq
    #
    @11
    cY
    wceq
    #
    @19
    @25
    wb
    wph
    @10
    cc0
    cX
    cY
    cs2
    #
    cfv
    #
    cX
    cc0
    cP
    @34
    1wlkd.p
    fveq1i
    wph
    cX
    cV
    wcel
    @35
    cX
    wceq
    1wlkd.x
    cX
    cY
    cV
    s2fv0
    syl
    syl5eq
    wph
    @11
    c1
    @34
    cfv
    #
    cY
    c1
    cP
    @34
    1wlkd.p
    fveq1i
    wph
    cY
    cV
    wcel
    @36
    cY
    wceq
    1wlkd.y
    cX
    cY
    cV
    s2fv1
    syl
    syl5eq
    @32
    @33
    wa
    #
    @12
    @16
    @18
    @20
    @22
    @24
    @10
    cX
    @11
    cY
    eqeq12
    @37
    @15
    @21
    @14
    @32
    @15
    @21
    wceq
    @33
    @10
    cX
    sneq
    adantr
    eqeq2d
    @37
    @17
    @23
    @14
    @10
    @11
    cX
    cY
    preq12
    sseq1d
    ifpbi123d
    syl2anc
    mpbird
    @5
    @19
    vk
    cc0
    c0ex
    @0
    cc0
    wceq
    #
    @2
    c1
    wceq
    @5
    @19
    wb
    @38
    @2
    cc0
    c1
    caddc
    co
    c1
    @0
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    @0
    cc0
    c1
    cP
    cF
    cI
    wkslem2
    mpdan
    ralsn
    sylibr
    wph
    @5
    vk
    @7
    @8
    @7
    @8
    wceq
    wph
    @7
    cc0
    c1
    cfzo
    co
    @8
    @6
    c1
    cc0
    cfzo
    @6
    @28
    chash
    cfv
    c1
    cF
    @28
    chash
    1wlkd.f
    fveq2i
    cJ
    s1len
    eqtri
    oveq2i
    fzo01
    eqtri
    a1i
    raleqdv
    mpbird
end
