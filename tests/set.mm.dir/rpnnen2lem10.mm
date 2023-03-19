include "wa.mm"
include "c1.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "csu.mm"
include "cuz.mm"
include "caddc.mm"
include "wceq.mm"
include "cn.mm"
include "simpr.mm"
include "sylib.mm"
include "wss.mm"
include "wcel.mm"
include "cdif.mm"
include "eldifi.mm"
include "ssel2.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "rpnnen2lem8.mm"
include "c3.mm"
include "cdiv.mm"
include "cexp.mm"
include "cc0.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "1z.mm"
include "nnz.mm"
include "elfzm11.mm"
include "sylancr.mm"
include "biimpa.mm"
include "sylan.mm"
include "simp3d.mm"
include "wi.mm"
include "wral.mm"
include "elfznn.mm"
include "breq1.mm"
include "eleq1.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "mpd.mm"
include "ifbid.mm"
include "rpnnen2lem1.mm"
include "3eqtr4d.mm"
include "sumeq2dv.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "cr.mm"
include "rpnnen2lem6.mm"
include "fzfid.mm"
include "wf.mm"
include "rpnnen2lem2.mm"
include "syl.mm"
include "ffvelrn.mm"
include "fsumrecl.mm"
include "readdcan.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem rpnnen2lem10
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )
  assume rpnnen2.2: |- ( ph -> A C_ NN )
  assume rpnnen2.3: |- ( ph -> B C_ NN )
  assume rpnnen2.4: |- ( ph -> m e. ( A \ B ) )
  assume rpnnen2.5: |- ( ph -> A. n e. NN ( n < m -> ( n e. A <-> n e. B ) ) )
  assume rpnnen2.6: |- ( ps <-> sum_ k e. NN ( ( F ` A ) ` k ) = sum_ k e. NN ( ( F ` B ) ` k ) )

  disjoint m n
  disjoint m x
  disjoint n x
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint F k
  disjoint F m
  disjoint k ph
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k y
  disjoint k z
  disjoint F y
  disjoint F z
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- ( ( ph /\ ps ) -> sum_ k e. ( ZZ>= ` m ) ( ( F ` A ) ` k ) = sum_ k e. ( ZZ>= ` m ) ( ( F ` B ) ` k ) )

  proof
    wph
    wps
    wa
    #
    c1
    vm
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cB
    cF
    cfv
    #
    cfv
    #
    vk
    csu
    #
    @1
    cuz
    cfv
    #
    @4
    cA
    cF
    cfv
    cfv
    #
    vk
    csu
    #
    caddc
    co
    #
    @7
    @8
    @6
    vk
    csu
    #
    caddc
    co
    #
    wceq
    #
    @10
    @12
    wceq
    #
    @0
    cn
    @9
    vk
    csu
    #
    cn
    @6
    vk
    csu
    #
    @11
    @13
    @0
    wps
    @16
    @17
    wceq
    wph
    wps
    simpr
    rpnnen2.6
    sylib
    wph
    @16
    @11
    wceq
    wps
    wph
    @16
    @3
    @9
    vk
    csu
    #
    @10
    caddc
    co
    #
    @11
    wph
    cA
    cn
    wss
    #
    @1
    cn
    wcel
    #
    @16
    @19
    wceq
    rpnnen2.2
    wph
    @20
    @1
    cA
    cB
    cdif
    wcel
    #
    @21
    rpnnen2.2
    rpnnen2.4
    @22
    @20
    @1
    cA
    wcel
    @21
    @1
    cA
    cB
    eldifi
    cA
    cn
    @1
    ssel2
    sylan2
    syl2anc
    #
    vx
    cA
    vk
    vn
    cF
    @1
    rpnnen2.1
    rpnnen2lem8
    syl2anc
    wph
    @18
    @7
    @10
    caddc
    wph
    @3
    @9
    @6
    vk
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @4
    cA
    wcel
    #
    c1
    c3
    cdiv
    co
    @4
    cexp
    co
    #
    cc0
    cif
    #
    @4
    cB
    wcel
    #
    @27
    cc0
    cif
    #
    @9
    @6
    @25
    @26
    @29
    @27
    cc0
    @25
    @4
    @1
    clt
    wbr
    #
    @26
    @29
    wb
    #
    @25
    @4
    cz
    wcel
    #
    c1
    @4
    cle
    wbr
    #
    @31
    wph
    @21
    @24
    @33
    @34
    @31
    w3a
    #
    @23
    @21
    @24
    @35
    @21
    c1
    cz
    wcel
    @1
    cz
    wcel
    @24
    @35
    wb
    1z
    @1
    nnz
    @4
    c1
    @1
    elfzm11
    sylancr
    biimpa
    sylan
    simp3d
    wph
    vn
    cv
    #
    @1
    clt
    wbr
    #
    @36
    cA
    wcel
    #
    @36
    cB
    wcel
    #
    wb
    #
    wi
    #
    vn
    cn
    wral
    @4
    cn
    wcel
    #
    @31
    @32
    wi
    #
    @24
    rpnnen2.5
    @4
    @2
    elfznn
    #
    @41
    @43
    vn
    @4
    cn
    @36
    @4
    wceq
    #
    @37
    @31
    @40
    @32
    @36
    @4
    @1
    clt
    breq1
    @45
    @38
    @26
    @39
    @29
    @36
    @4
    cA
    eleq1
    @36
    @4
    cB
    eleq1
    bibi12d
    imbi12d
    rspccva
    syl2an
    mpd
    ifbid
    wph
    @20
    @42
    @9
    @28
    wceq
    @24
    rpnnen2.2
    @44
    vx
    cA
    vn
    cF
    @4
    rpnnen2.1
    rpnnen2lem1
    syl2an
    wph
    cB
    cn
    wss
    #
    @42
    @6
    @30
    wceq
    @24
    rpnnen2.3
    @44
    vx
    cB
    vn
    cF
    @4
    rpnnen2.1
    rpnnen2lem1
    syl2an
    3eqtr4d
    sumeq2dv
    oveq1d
    eqtrd
    adantr
    wph
    @17
    @13
    wceq
    #
    wps
    wph
    @46
    @21
    @47
    rpnnen2.3
    @23
    vx
    cB
    vk
    vn
    cF
    @1
    rpnnen2.1
    rpnnen2lem8
    syl2anc
    adantr
    3eqtr3d
    wph
    @14
    @15
    wb
    #
    wps
    wph
    @10
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @7
    cr
    wcel
    @48
    wph
    @20
    @21
    @49
    rpnnen2.2
    @23
    vx
    cA
    vk
    vn
    cF
    @1
    rpnnen2.1
    rpnnen2lem6
    syl2anc
    wph
    @46
    @21
    @50
    rpnnen2.3
    @23
    vx
    cB
    vk
    vn
    cF
    @1
    rpnnen2.1
    rpnnen2lem6
    syl2anc
    wph
    @3
    @6
    vk
    wph
    c1
    @2
    fzfid
    wph
    cn
    cr
    @5
    wf
    #
    @42
    @6
    cr
    wcel
    @24
    wph
    @46
    @51
    rpnnen2.3
    vx
    cB
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    syl
    @44
    cn
    cr
    @4
    @5
    ffvelrn
    syl2an
    fsumrecl
    @10
    @12
    @7
    readdcan
    syl3anc
    adantr
    mpbid
end
