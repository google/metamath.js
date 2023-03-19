include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "citg2.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "adantr.mm"
include "adantlr.mm"
include "iexpcyc.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "ad2antlr.mm"
include "eqtr4d.mm"
include "ibllem.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "c1.mm"
include "cmin.mm"
include "cn.mm"
include "4nn.mm"
include "zmodfz.mm"
include "mpan2.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "caddc.mm"
include "addcomi.mm"
include "df-4.mm"
include "eqtr4i.mm"
include "subaddrii.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "cmbf.mm"
include "cibl.mm"
include "eqidd.mm"
include "isibl2.mm"
include "mpbid.mm"
include "simprd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "ifbieq1d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"

theorem iblitg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cG: class G
  let cK: class K
  let cV: class V
  let vf: setvar f
  let vk: setvar k
  let vy: setvar y
  assume iblitg.1: |- ( ph -> G = ( x e. RR |-> if ( ( x e. A /\ 0 <_ T ) , T , 0 ) ) )
  assume iblitg.2: |- ( ( ph /\ x e. A ) -> T = ( Re ` ( B / ( _i ^ K ) ) ) )
  assume iblitg.3: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume iblitg.4: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A x
  disjoint K x
  disjoint ph x
  disjoint V x
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint B k
  disjoint B y
  disjoint G k
  disjoint K k
  disjoint K y
  disjoint k ph
  disjoint ph y
  disjoint T y
  assert |- ( ( ph /\ K e. ZZ ) -> ( S.2 ` G ) e. RR )

  proof
    wph
    cK
    cz
    wcel
    #
    wa
    #
    cG
    citg2
    cfv
    vx
    cr
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    ci
    cK
    c4
    cmo
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    @1
    cG
    @10
    citg2
    @1
    cG
    vx
    cr
    @2
    cc0
    cT
    cle
    wbr
    wa
    cT
    cc0
    cif
    #
    cmpt
    #
    @10
    wph
    cG
    @13
    wceq
    @0
    iblitg.1
    adantr
    @1
    vx
    cr
    @12
    @9
    @1
    vx
    cA
    cT
    @6
    @1
    @2
    wa
    cT
    cB
    ci
    cK
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    @6
    wph
    @2
    cT
    @16
    wceq
    @0
    iblitg.2
    adantlr
    @0
    @6
    @16
    wceq
    wph
    @2
    @0
    @5
    @15
    cre
    @0
    @4
    @14
    cB
    cdiv
    cK
    iexpcyc
    oveq2d
    fveq2d
    ad2antlr
    eqtr4d
    ibllem
    mpteq2dv
    eqtrd
    fveq2d
    @1
    @3
    cc0
    c3
    cfz
    co
    #
    wcel
    #
    vx
    cr
    @2
    cc0
    cB
    ci
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @22
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vk
    @17
    wral
    #
    @11
    cr
    wcel
    #
    @0
    @18
    wph
    @0
    @3
    cc0
    c4
    c1
    cmin
    co
    #
    cfz
    co
    #
    @17
    @0
    c4
    cn
    wcel
    @3
    @32
    wcel
    4nn
    cK
    c4
    zmodfz
    mpan2
    @31
    c3
    cc0
    cfz
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    c1
    c3
    caddc
    co
    c3
    c1
    caddc
    co
    c4
    c1
    c3
    ax-1cn
    3cn
    addcomi
    df-4
    eqtr4i
    subaddrii
    oveq2i
    syl6eleq
    adantl
    wph
    @29
    @0
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @29
    wph
    @33
    cibl
    wcel
    @34
    @29
    wa
    iblitg.3
    wph
    vx
    cA
    cB
    @22
    vk
    @26
    cV
    wph
    @26
    eqidd
    wph
    @2
    wa
    @22
    eqidd
    iblitg.4
    isibl2
    mpbid
    simprd
    adantr
    @28
    @30
    vk
    @3
    @17
    @19
    @3
    wceq
    #
    @27
    @11
    cr
    @35
    @26
    @10
    citg2
    @35
    vx
    cr
    @25
    @9
    @35
    @24
    @8
    @22
    @6
    cc0
    @35
    @23
    @7
    @2
    @35
    @22
    @6
    cc0
    cle
    @35
    @21
    @5
    cre
    @35
    @20
    @4
    cB
    cdiv
    @19
    @3
    ci
    cexp
    oveq2
    oveq2d
    fveq2d
    #
    breq2d
    anbi2d
    @36
    ifbieq1d
    mpteq2dv
    fveq2d
    eleq1d
    rspcv
    sylc
    eqeltrd
end
