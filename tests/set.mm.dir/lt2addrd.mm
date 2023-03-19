include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "w3a.mm"
include "wrex.mm"
include "readdcld.mm"
include "resubcld.mm"
include "rehalfcld.mm"
include "recnd.mm"
include "addcld.mm"
include "subcld.mm"
include "halfcld.mm"
include "subsub4d.mm"
include "oveq2d.mm"
include "subadd23d.mm"
include "cc.mm"
include "2halvesd.mm"
include "eqeltrd.mm"
include "addsubassd.mm"
include "3eqtr4d.mm"
include "nncand.mm"
include "3eqtrrd.mm"
include "crp.mm"
include "wb.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rphalfcld.mm"
include "ltsubrpd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "breq1.mm"
include "3anbi12d.mm"
include "oveq2.mm"
include "3anbi13d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"

theorem lt2addrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vc: setvar c
  assume lt2addrd.1: |- ( ph -> A e. RR )
  assume lt2addrd.2: |- ( ph -> B e. RR )
  assume lt2addrd.3: |- ( ph -> C e. RR )
  assume lt2addrd.4: |- ( ph -> A < ( B + C ) )

  disjoint b c
  disjoint A b
  disjoint A c
  disjoint B b
  disjoint B c
  disjoint C b
  disjoint C c
  assert |- ( ph -> E. b e. RR E. c e. RR ( A = ( b + c ) /\ b < B /\ c < C ) )

  proof
    wph
    cB
    cB
    cC
    caddc
    co
    #
    cA
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cr
    wcel
    cC
    @2
    cmin
    co
    #
    cr
    wcel
    cA
    @3
    @4
    caddc
    co
    #
    wceq
    #
    @3
    cB
    clt
    wbr
    #
    @4
    cC
    clt
    wbr
    #
    cA
    vb
    cv
    #
    vc
    cv
    #
    caddc
    co
    #
    wceq
    #
    @9
    cB
    clt
    wbr
    #
    @10
    cC
    clt
    wbr
    #
    w3a
    #
    vc
    cr
    wrex
    vb
    cr
    wrex
    wph
    cB
    @2
    lt2addrd.2
    wph
    @1
    wph
    @0
    cA
    wph
    cB
    cC
    lt2addrd.2
    lt2addrd.3
    readdcld
    #
    lt2addrd.1
    resubcld
    rehalfcld
    #
    resubcld
    wph
    cC
    @2
    lt2addrd.3
    @17
    resubcld
    wph
    @5
    @0
    @2
    @2
    caddc
    co
    #
    cmin
    co
    #
    @0
    @1
    cmin
    co
    cA
    wph
    cB
    @4
    @2
    cmin
    co
    #
    caddc
    co
    cB
    cC
    @18
    cmin
    co
    #
    caddc
    co
    @5
    @19
    wph
    @20
    @21
    cB
    caddc
    wph
    cC
    @2
    @2
    wph
    cC
    lt2addrd.3
    recnd
    #
    wph
    @1
    wph
    @0
    cA
    wph
    cB
    cC
    wph
    cB
    lt2addrd.2
    recnd
    #
    @22
    addcld
    #
    wph
    cA
    lt2addrd.1
    recnd
    #
    subcld
    #
    halfcld
    #
    @27
    subsub4d
    oveq2d
    wph
    cB
    @2
    @4
    @23
    @27
    wph
    cC
    @2
    @22
    @27
    subcld
    subadd23d
    wph
    cB
    cC
    @18
    @23
    @22
    wph
    @18
    @1
    cc
    wph
    @1
    @26
    2halvesd
    #
    @26
    eqeltrd
    addsubassd
    3eqtr4d
    wph
    @18
    @1
    @0
    cmin
    @28
    oveq2d
    wph
    @0
    cA
    @24
    @25
    nncand
    3eqtrrd
    wph
    cB
    @2
    lt2addrd.2
    wph
    @1
    wph
    cA
    @0
    clt
    wbr
    #
    @1
    crp
    wcel
    #
    lt2addrd.4
    wph
    cA
    cr
    wcel
    @0
    cr
    wcel
    @29
    @30
    wb
    lt2addrd.1
    @16
    cA
    @0
    difrp
    syl2anc
    mpbid
    rphalfcld
    #
    ltsubrpd
    wph
    cC
    @2
    lt2addrd.3
    @31
    ltsubrpd
    @15
    @6
    @7
    @8
    w3a
    cA
    @3
    @10
    caddc
    co
    #
    wceq
    #
    @7
    @14
    w3a
    vb
    vc
    @3
    @4
    cr
    cr
    @9
    @3
    wceq
    #
    @12
    @33
    @13
    @7
    @14
    @34
    @11
    @32
    cA
    @9
    @3
    @10
    caddc
    oveq1
    eqeq2d
    @9
    @3
    cB
    clt
    breq1
    3anbi12d
    @10
    @4
    wceq
    #
    @33
    @6
    @14
    @8
    @7
    @35
    @32
    @5
    cA
    @10
    @4
    @3
    caddc
    oveq2
    eqeq2d
    @10
    @4
    cC
    clt
    breq1
    3anbi13d
    rspc2ev
    syl113anc
end
