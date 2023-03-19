include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cmpt.mm"
include "clo1.mm"
include "wcel.mm"
include "ello1mpt2.mm"
include "mpbid.mm"
include "wa.mm"
include "cif.mm"
include "wb.mm"
include "elicopnf.mm"
include "syl.mm"
include "biimpa.mm"
include "syldan.mm"
include "ad2antrr.mm"
include "wn.mm"
include "simplrl.mm"
include "ifclda.mm"
include "clt.mm"
include "wss.mm"
include "sselda.mm"
include "simpld.mm"
include "ltnled.mm"
include "expr.mm"
include "an32s.mm"
include "ex.mm"
include "imp.mm"
include "adantlr.mm"
include "simplr.mm"
include "max2.mm"
include "syl2anc.mm"
include "simpll.mm"
include "sylan.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "sylbird.mm"
include "max1.mm"
include "jad.mm"
include "ralimdva.mm"
include "impr.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem lo1bdd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let cM: class M
  let vn: setvar n
  assume lo1bdd2.1: |- ( ph -> A C_ RR )
  assume lo1bdd2.2: |- ( ph -> C e. RR )
  assume lo1bdd2.3: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume lo1bdd2.4: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1bdd2.5: |- ( ( ph /\ ( y e. RR /\ C <_ y ) ) -> M e. RR )
  assume lo1bdd2.6: |- ( ( ( ph /\ x e. A ) /\ ( ( y e. RR /\ C <_ y ) /\ x < y ) ) -> B <_ M )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint M m
  disjoint M x
  disjoint m n
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint B n
  disjoint C n
  disjoint n ph
  disjoint M n
  assert |- ( ph -> E. m e. RR A. x e. A B <_ m )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    vn
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vn
    cr
    wrex
    #
    vy
    cC
    cpnf
    cico
    co
    #
    wrex
    #
    cB
    vm
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vm
    cr
    wrex
    #
    wph
    vx
    cA
    cB
    cmpt
    clo1
    wcel
    @9
    lo1bdd2.4
    wph
    vx
    vy
    cA
    cB
    cC
    vn
    lo1bdd2.1
    lo1bdd2.3
    lo1bdd2.2
    ello1mpt2
    mpbid
    wph
    @7
    @13
    vy
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @6
    @13
    vn
    cr
    @15
    @3
    cr
    wcel
    #
    @6
    @13
    @15
    @16
    @6
    wa
    #
    wa
    #
    @3
    cM
    cle
    wbr
    #
    cM
    @3
    cif
    #
    cr
    wcel
    #
    cB
    @20
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @13
    @18
    @19
    cM
    @3
    cr
    @15
    cM
    cr
    wcel
    #
    @17
    @19
    wph
    @14
    @0
    cr
    wcel
    #
    cC
    @0
    cle
    wbr
    #
    wa
    #
    @24
    wph
    @14
    @27
    wph
    cC
    cr
    wcel
    @14
    @27
    wb
    lo1bdd2.2
    cC
    @0
    elicopnf
    syl
    biimpa
    #
    lo1bdd2.5
    syldan
    #
    ad2antrr
    @15
    @16
    @6
    @19
    wn
    #
    simplrl
    ifclda
    @15
    @16
    @6
    @23
    @15
    @16
    wa
    #
    @5
    @22
    vx
    cA
    @31
    @1
    cA
    wcel
    #
    wa
    #
    @2
    @4
    @22
    @33
    @2
    wn
    @1
    @0
    clt
    wbr
    #
    @22
    @33
    @1
    @0
    @31
    cA
    cr
    @1
    wph
    cA
    cr
    wss
    @14
    @16
    lo1bdd2.1
    ad2antrr
    sselda
    @15
    @25
    @16
    @32
    @15
    @25
    @26
    @28
    simpld
    ad2antrr
    ltnled
    @33
    @34
    cB
    cM
    cle
    wbr
    #
    @22
    @15
    @32
    @34
    @35
    wi
    #
    @16
    @15
    @32
    @36
    wph
    @14
    @27
    @32
    @36
    wi
    @28
    wph
    @27
    wa
    @32
    @36
    wph
    @32
    @27
    @36
    wph
    @32
    wa
    @27
    @34
    @35
    lo1bdd2.6
    expr
    an32s
    ex
    syldan
    imp
    adantlr
    @33
    @35
    cM
    @20
    cle
    wbr
    #
    @22
    @33
    @16
    @24
    @37
    @15
    @16
    @32
    simplr
    #
    @15
    @24
    @16
    @32
    @29
    ad2antrr
    #
    @3
    cM
    max2
    syl2anc
    @33
    cB
    cr
    wcel
    #
    @24
    @21
    @35
    @37
    wa
    @22
    wi
    @31
    wph
    @32
    @40
    wph
    @14
    @16
    simpll
    lo1bdd2.3
    sylan
    #
    @39
    @33
    @19
    cM
    @3
    cr
    @15
    @24
    @16
    @32
    @19
    @29
    ad3antrrr
    @15
    @16
    @32
    @30
    simpllr
    ifclda
    #
    cB
    cM
    @20
    letr
    syl3anc
    mpan2d
    syld
    sylbird
    @33
    @4
    @3
    @20
    cle
    wbr
    #
    @22
    @33
    @16
    @24
    @43
    @38
    @39
    @3
    cM
    max1
    syl2anc
    @33
    @40
    @16
    @21
    @4
    @43
    wa
    @22
    wi
    @41
    @38
    @42
    cB
    @3
    @20
    letr
    syl3anc
    mpan2d
    jad
    ralimdva
    impr
    @12
    @23
    vm
    @20
    cr
    @10
    @20
    wceq
    @11
    @22
    vx
    cA
    @10
    @20
    cB
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    expr
    rexlimdva
    rexlimdva
    mpd
end
