include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cbl.mm"
include "wss.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cxp.mm"
include "c2nd.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "ccl.mm"
include "cdif.mm"
include "w3a.mm"
include "wral.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "bcthlem1.mm"
include "expr.mm"
include "mpd.mm"
include "mpbid.mm"
include "wi.mm"
include "ctop.mm"
include "cuni.mm"
include "cxmt.mm"
include "cme.mm"
include "cms.mm"
include "cmetmet.mm"
include "syl.mm"
include "metxmet.mm"
include "mopntop.mm"
include "adantr.mm"
include "c1st.mm"
include "cxr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "rpxrd.mm"
include "jca.mm"
include "blssm.mm"
include "3expb.mm"
include "syl2an.mm"
include "cop.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "syl6reqr.mm"
include "adantl.mm"
include "mopnuni.mm"
include "3sstr3d.mm"
include "eqid.mm"
include "sscls.mm"
include "syl2anc.mm"
include "difss2.mm"
include "sstr2.mm"
include "syl2im.mm"
include "a1d.mm"
include "ex.mm"
include "3impd.mm"
include "ralrimiva.mm"

theorem bcthlem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let cD: class D
  let cR: class R
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vr: setvar r
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vy: setvar y
  assume bcth.2: |- J = ( MetOpen ` D )
  assume bcthlem.4: |- ( ph -> D e. ( CMet ` X ) )
  assume bcthlem.5: |- F = ( k e. NN , z e. ( X X. RR+ ) |-> { <. x , r >. | ( ( x e. X /\ r e. RR+ ) /\ ( r < ( 1 / k ) /\ ( ( cls ` J ) ` ( x ( ball ` D ) r ) ) C_ ( ( ( ball ` D ) ` z ) \ ( M ` k ) ) ) ) } )
  assume bcthlem.6: |- ( ph -> M : NN --> ( Clsd ` J ) )
  assume bcthlem.7: |- ( ph -> R e. RR+ )
  assume bcthlem.8: |- ( ph -> C e. X )
  assume bcthlem.9: |- ( ph -> g : NN --> ( X X. RR+ ) )
  assume bcthlem.10: |- ( ph -> ( g ` 1 ) = <. C , R >. )
  assume bcthlem.11: |- ( ph -> A. k e. NN ( g ` ( k + 1 ) ) e. ( k F ( g ` k ) ) )

  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k z
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g x
  disjoint g z
  disjoint D g
  disjoint D k
  disjoint D n
  disjoint D r
  disjoint D x
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J k
  disjoint J n
  disjoint J r
  disjoint J x
  disjoint J z
  disjoint M g
  disjoint M k
  disjoint M n
  disjoint M r
  disjoint M x
  disjoint M z
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint A k
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint g m
  disjoint g y
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint r y
  disjoint x y
  disjoint y z
  disjoint D y
  disjoint J m
  disjoint J y
  disjoint M m
  disjoint M y
  disjoint m ph
  disjoint X m
  disjoint X y
  assert |- ( ph -> A. n e. NN ( ( ball ` D ) ` ( g ` ( n + 1 ) ) ) C_ ( ( ball ` D ) ` ( g ` n ) ) )

  proof
    wph
    vn
    cv
    #
    c1
    caddc
    co
    #
    vg
    cv
    #
    cfv
    #
    cD
    cbl
    cfv
    #
    cfv
    #
    @0
    @2
    cfv
    #
    @4
    cfv
    #
    wss
    #
    vn
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @3
    cX
    crp
    cxp
    #
    wcel
    #
    @3
    c2nd
    cfv
    #
    c1
    @0
    cdiv
    co
    clt
    wbr
    #
    @5
    cJ
    ccl
    cfv
    cfv
    #
    @7
    @0
    cM
    cfv
    #
    cdif
    wss
    #
    w3a
    #
    @8
    @10
    @3
    @0
    @6
    cF
    co
    #
    wcel
    #
    @18
    wph
    vk
    cv
    #
    c1
    caddc
    co
    #
    @2
    cfv
    #
    @21
    @21
    @2
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    cn
    wral
    @9
    @20
    bcthlem.11
    @26
    @20
    vk
    @0
    cn
    @21
    @0
    wceq
    #
    @23
    @3
    @25
    @19
    @27
    @22
    @1
    @2
    @21
    @0
    c1
    caddc
    oveq1
    fveq2d
    @27
    @21
    @0
    @24
    @6
    cF
    @27
    id
    @21
    @0
    @2
    fveq2
    oveq12d
    eleq12d
    rspccva
    sylan
    @10
    @6
    @11
    wcel
    #
    @20
    @18
    wb
    #
    wph
    cn
    @11
    @0
    @2
    bcthlem.9
    ffvelrnda
    wph
    @9
    @28
    @29
    wph
    vx
    vz
    @0
    @6
    @3
    cD
    vk
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem1
    expr
    mpd
    mpbid
    wph
    @18
    @8
    wi
    @9
    wph
    @12
    @14
    @17
    @8
    wph
    @12
    @14
    @17
    @8
    wi
    #
    wi
    wph
    @12
    wa
    #
    @30
    @14
    @31
    @5
    @15
    wss
    #
    @17
    @15
    @7
    wss
    @8
    @31
    cJ
    ctop
    wcel
    #
    @5
    cJ
    cuni
    #
    wss
    @32
    wph
    @33
    @12
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @33
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @35
    wph
    cD
    cX
    cms
    cfv
    wcel
    @36
    bcthlem.4
    cD
    cX
    cmetmet
    syl
    cD
    cX
    metxmet
    syl
    #
    cD
    cJ
    cX
    bcth.2
    mopntop
    syl
    adantr
    @31
    @3
    c1st
    cfv
    #
    @13
    @4
    co
    #
    cX
    @5
    @34
    wph
    @35
    @38
    cX
    wcel
    #
    @13
    cxr
    wcel
    #
    wa
    @39
    cX
    wss
    #
    @12
    @37
    @12
    @40
    @41
    @3
    cX
    crp
    xp1st
    @12
    @13
    @3
    cX
    crp
    xp2nd
    rpxrd
    jca
    @35
    @40
    @41
    @42
    cD
    @38
    @13
    cX
    blssm
    3expb
    syl2an
    @12
    @39
    @5
    wceq
    wph
    @12
    @5
    @38
    @13
    cop
    #
    @4
    cfv
    @39
    @12
    @3
    @43
    @4
    @3
    cX
    crp
    1st2nd2
    fveq2d
    @38
    @13
    @4
    df-ov
    syl6reqr
    adantl
    wph
    cX
    @34
    wceq
    #
    @12
    wph
    @35
    @44
    @37
    cD
    cJ
    cX
    bcth.2
    mopnuni
    syl
    adantr
    3sstr3d
    @5
    cJ
    @34
    @34
    eqid
    sscls
    syl2anc
    @15
    @7
    @16
    difss2
    @5
    @15
    @7
    sstr2
    syl2im
    a1d
    ex
    3impd
    adantr
    mpd
    ralrimiva
end
