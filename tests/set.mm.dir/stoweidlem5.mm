include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "halfre.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "ifcl.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "rpred.mm"
include "cr.mm"
include "a1i.mm"
include "1red.mm"
include "min2.mm"
include "syl5eqbr.mm"
include "halflt1.mm"
include "lelttrd.mm"
include "wa.mm"
include "adantr.mm"
include "wf.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "min1.mm"
include "r19.21bi.mm"
include "letrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "breq1.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "syl.mm"
include "mp3and.mm"

theorem stoweidlem5
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem5.1: |- F/ t ph
  assume stoweidlem5.2: |- D = if ( C <_ ( 1 / 2 ) , C , ( 1 / 2 ) )
  assume stoweidlem5.3: |- ( ph -> P : T --> RR )
  assume stoweidlem5.4: |- ( ph -> Q C_ T )
  assume stoweidlem5.5: |- ( ph -> C e. RR+ )
  assume stoweidlem5.6: |- ( ph -> A. t e. Q C <_ ( P ` t ) )

  disjoint d t
  disjoint D d
  disjoint D t
  disjoint P d
  disjoint Q d
  disjoint k x
  assert |- ( ph -> E. d ( d e. RR+ /\ d < 1 /\ A. t e. Q d <_ ( P ` t ) ) )

  proof
    wph
    cD
    crp
    wcel
    #
    cD
    c1
    clt
    wbr
    #
    cD
    vt
    cv
    #
    cP
    cfv
    #
    cle
    wbr
    #
    vt
    cQ
    wral
    #
    vd
    cv
    #
    crp
    wcel
    #
    @6
    c1
    clt
    wbr
    #
    @6
    @3
    cle
    wbr
    #
    vt
    cQ
    wral
    #
    w3a
    #
    vd
    wex
    #
    wph
    cD
    cC
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    cC
    @13
    cif
    #
    crp
    stoweidlem5.2
    wph
    cC
    crp
    wcel
    @13
    crp
    wcel
    @15
    crp
    wcel
    stoweidlem5.5
    @13
    halfre
    halfgt0
    elrpii
    @14
    cC
    @13
    crp
    ifcl
    sylancl
    #
    syl5eqel
    #
    wph
    cD
    @13
    c1
    wph
    cD
    @17
    rpred
    @13
    cr
    wcel
    #
    wph
    halfre
    a1i
    wph
    1red
    wph
    cD
    @15
    @13
    cle
    stoweidlem5.2
    wph
    cC
    cr
    wcel
    #
    @18
    @15
    @13
    cle
    wbr
    wph
    cC
    stoweidlem5.5
    rpred
    #
    halfre
    cC
    @13
    min2
    sylancl
    syl5eqbr
    @13
    c1
    clt
    wbr
    wph
    halflt1
    a1i
    lelttrd
    wph
    @4
    vt
    cQ
    stoweidlem5.1
    wph
    @2
    cQ
    wcel
    #
    @4
    wph
    @21
    wa
    #
    cD
    @15
    @3
    cle
    stoweidlem5.2
    @22
    @15
    cC
    @3
    wph
    @15
    cr
    wcel
    @21
    wph
    @15
    @16
    rpred
    adantr
    wph
    @19
    @21
    @20
    adantr
    @22
    cT
    cr
    @2
    cP
    wph
    cT
    cr
    cP
    wf
    @21
    stoweidlem5.3
    adantr
    wph
    cQ
    cT
    @2
    stoweidlem5.4
    sselda
    ffvelrnd
    wph
    @15
    cC
    cle
    wbr
    #
    @21
    wph
    @19
    @18
    @23
    @20
    halfre
    cC
    @13
    min1
    sylancl
    adantr
    wph
    cC
    @3
    cle
    wbr
    vt
    cQ
    stoweidlem5.6
    r19.21bi
    letrd
    syl5eqbr
    ex
    ralrimi
    wph
    @0
    @0
    @1
    @5
    w3a
    #
    @12
    wi
    @17
    @11
    @24
    vd
    cD
    crp
    @6
    cD
    wceq
    #
    @7
    @0
    @8
    @1
    @10
    @5
    @6
    cD
    crp
    eleq1
    @6
    cD
    c1
    clt
    breq1
    @25
    @9
    @4
    vt
    cQ
    @6
    cD
    @3
    cle
    breq1
    ralbidv
    3anbi123d
    spcegv
    syl
    mp3and
end
