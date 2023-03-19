include "c1st.mm"
include "cv.mm"
include "ccom.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cbl.mm"
include "ccl.mm"
include "wss.mm"
include "wa.mm"
include "crp.mm"
include "cxp.mm"
include "c2nd.mm"
include "cdiv.mm"
include "clt.mm"
include "cdif.mm"
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
include "simp3d.mm"
include "difss2d.mm"
include "3adant2.mm"
include "peano2nn.mm"
include "cms.mm"
include "cme.mm"
include "cxmt.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "bcthlem2.mm"
include "caublcls.mm"
include "syl3an3.mm"
include "sseldd.mm"

theorem bcthlem3
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vn: setvar n
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

  disjoint k r
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint r x
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g r
  disjoint g x
  disjoint g z
  disjoint D g
  disjoint D k
  disjoint D r
  disjoint D x
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J k
  disjoint J r
  disjoint J x
  disjoint J z
  disjoint M g
  disjoint M k
  disjoint M r
  disjoint M x
  disjoint M z
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X k
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint k n
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint g m
  disjoint g n
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
  disjoint D n
  disjoint r y
  disjoint x y
  disjoint y z
  disjoint D y
  disjoint F n
  disjoint J m
  disjoint J n
  disjoint J y
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint m ph
  disjoint n ph
  disjoint X m
  disjoint X n
  disjoint X y
  assert |- ( ( ph /\ ( 1st o. g ) ( ~~>t ` J ) x /\ A e. NN ) -> x e. ( ( ball ` D ) ` ( g ` A ) ) )

  proof
    wph
    c1st
    vg
    cv
    #
    ccom
    vx
    cv
    #
    cJ
    clm
    cfv
    wbr
    #
    cA
    cn
    wcel
    #
    w3a
    cA
    c1
    caddc
    co
    #
    @0
    cfv
    #
    cD
    cbl
    cfv
    #
    cfv
    cJ
    ccl
    cfv
    cfv
    #
    cA
    @0
    cfv
    #
    @6
    cfv
    #
    @1
    wph
    @3
    @7
    @9
    wss
    @2
    wph
    @3
    wa
    #
    @7
    @9
    cA
    cM
    cfv
    #
    @10
    @5
    cX
    crp
    cxp
    #
    wcel
    #
    @5
    c2nd
    cfv
    c1
    cA
    cdiv
    co
    clt
    wbr
    #
    @7
    @9
    @11
    cdif
    wss
    #
    @10
    @5
    cA
    @8
    cF
    co
    #
    wcel
    #
    @13
    @14
    @15
    w3a
    #
    wph
    vk
    cv
    #
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @19
    @19
    @0
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
    @3
    @17
    bcthlem.11
    @24
    @17
    vk
    cA
    cn
    @19
    cA
    wceq
    #
    @21
    @5
    @23
    @16
    @25
    @20
    @4
    @0
    @19
    cA
    c1
    caddc
    oveq1
    fveq2d
    @25
    @19
    cA
    @22
    @8
    cF
    @25
    id
    @19
    cA
    @0
    fveq2
    oveq12d
    eleq12d
    rspccva
    sylan
    @10
    @8
    @12
    wcel
    #
    @17
    @18
    wb
    #
    wph
    cn
    @12
    cA
    @0
    bcthlem.9
    ffvelrnda
    wph
    @3
    @26
    @27
    wph
    vx
    vz
    cA
    @8
    @5
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
    simp3d
    difss2d
    3adant2
    @3
    wph
    @2
    @4
    cn
    wcel
    @1
    @7
    wcel
    cA
    peano2nn
    wph
    @4
    cD
    @1
    vn
    @0
    cJ
    cX
    wph
    cD
    cX
    cms
    cfv
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cD
    cX
    cxmt
    cfv
    wcel
    bcthlem.4
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    bcthlem.9
    wph
    vx
    vz
    cC
    cD
    cR
    vg
    vk
    vn
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    bcthlem.4
    bcthlem.5
    bcthlem.6
    bcthlem.7
    bcthlem.8
    bcthlem.9
    bcthlem.10
    bcthlem.11
    bcthlem2
    bcth.2
    caublcls
    syl3an3
    sseldd
end
