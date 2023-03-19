include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "nnred.mm"
include "remulcld.mm"
include "cc0.mm"
include "clt.mm"
include "2pos.mm"
include "nngt0d.mm"
include "mulgt0d.mm"
include "gt0ne0d.mm"
include "nn0zd.mm"
include "znegcld.mm"
include "reexpclzd.mm"
include "recnd.mm"
include "mulne0bad.mm"
include "redivcld.mm"
include "w3a.mm"
include "3jca.mm"
include "expgt0.mm"
include "syl.mm"
include "divgt0d.mm"
include "flcld.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "id.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "zred.mm"
include "0red.mm"
include "ltled.mm"
include "flle.mm"
include "lemul2ad.mm"
include "divcan2d.mm"
include "breqtrd.mm"
include "eqcomd.mm"
include "peano2re.mm"
include "fllep1.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "rspcedvd.mm"

theorem knoppndvlem19
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vm: setvar m
  let cH: class H
  let cJ: class J
  let cN: class N
  assume knoppndvlem19.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. m )
  assume knoppndvlem19.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( m + 1 ) )
  assume knoppndvlem19.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem19.h: |- ( ph -> H e. RR )
  assume knoppndvlem19.n: |- ( ph -> N e. NN )

  disjoint m ph
  disjoint J m
  disjoint H m
  disjoint N m
  assert |- ( ph -> E. m e. ZZ ( A <_ H /\ H <_ B ) )

  proof
    wph
    cA
    cH
    cle
    wbr
    #
    cH
    cB
    cle
    wbr
    #
    wa
    #
    c2
    cN
    cmul
    co
    #
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cH
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cH
    cle
    wbr
    #
    cH
    @6
    @8
    c1
    caddc
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    vm
    @8
    cz
    wph
    @7
    wph
    cH
    @6
    knoppndvlem19.h
    wph
    @5
    c2
    wph
    @3
    @4
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cN
    knoppndvlem19.n
    nnred
    #
    remulcld
    #
    wph
    @3
    wph
    c2
    cN
    @15
    @16
    cc0
    c2
    clt
    wbr
    wph
    2pos
    a1i
    #
    wph
    cN
    knoppndvlem19.n
    nngt0d
    mulgt0d
    #
    gt0ne0d
    #
    wph
    cJ
    wph
    cJ
    knoppndvlem19.j
    nn0zd
    znegcld
    #
    reexpclzd
    #
    @15
    wph
    c2
    cN
    wph
    c2
    @15
    recnd
    wph
    cN
    @16
    recnd
    @20
    mulne0bad
    redivcld
    #
    wph
    @6
    wph
    @5
    c2
    @22
    @15
    wph
    @3
    cr
    wcel
    #
    @4
    cz
    wcel
    #
    cc0
    @3
    clt
    wbr
    #
    w3a
    cc0
    @5
    clt
    wbr
    wph
    @24
    @25
    @26
    @17
    @21
    @19
    3jca
    @3
    @4
    expgt0
    syl
    @18
    divgt0d
    #
    gt0ne0d
    #
    redivcld
    #
    flcld
    #
    vm
    cv
    #
    @8
    wceq
    #
    @2
    @14
    wb
    wph
    @32
    @0
    @10
    @1
    @13
    @32
    cA
    @9
    cH
    cle
    @32
    cA
    @6
    @31
    cmul
    co
    #
    @9
    cA
    @33
    wceq
    @32
    knoppndvlem19.a
    a1i
    @32
    @31
    @8
    @6
    cmul
    @32
    id
    #
    oveq2d
    eqtrd
    breq1d
    @32
    cB
    @12
    cH
    cle
    @32
    cB
    @6
    @31
    c1
    caddc
    co
    #
    cmul
    co
    #
    @12
    cB
    @36
    wceq
    @32
    knoppndvlem19.b
    a1i
    @32
    @35
    @11
    @6
    cmul
    @32
    @31
    @8
    c1
    caddc
    @34
    oveq1d
    oveq2d
    eqtrd
    breq2d
    anbi12d
    adantl
    wph
    @10
    @13
    wph
    @9
    @6
    @7
    cmul
    co
    #
    cH
    cle
    wph
    @8
    @7
    @6
    wph
    @8
    @30
    zred
    #
    @29
    @23
    wph
    cc0
    @6
    wph
    0red
    @23
    @27
    ltled
    #
    wph
    @7
    cr
    wcel
    #
    @8
    @7
    cle
    wbr
    @29
    @7
    flle
    syl
    lemul2ad
    wph
    cH
    @6
    wph
    cH
    knoppndvlem19.h
    recnd
    wph
    @6
    @23
    recnd
    @28
    divcan2d
    #
    breqtrd
    wph
    cH
    @37
    @12
    cle
    wph
    @37
    cH
    @41
    eqcomd
    wph
    @7
    @11
    @6
    @29
    wph
    @8
    cr
    wcel
    @11
    cr
    wcel
    @38
    @8
    peano2re
    syl
    @23
    @39
    wph
    @40
    @7
    @11
    cle
    wbr
    @29
    @7
    fllep1
    syl
    lemul2ad
    eqbrtrd
    jca
    rspcedvd
end
