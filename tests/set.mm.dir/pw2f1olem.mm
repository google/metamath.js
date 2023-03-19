include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "cpr.mm"
include "wf.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "prid2g.mm"
include "syl.mm"
include "prid1g.mm"
include "ifcld.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "simprr.mm"
include "feq1d.mm"
include "mpbird.mm"
include "cfv.mm"
include "iftrue.mm"
include "wne.mm"
include "wn.mm"
include "ad2antrr.mm"
include "iffalse.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "necon4bd.mm"
include "impbid2.mm"
include "simplrr.mm"
include "fveq1d.mm"
include "id.mm"
include "eleq1.mm"
include "ifbid.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "simprl.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "jca.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "ad2antrl.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "dffn5.mm"
include "sylib.mm"
include "eleq2d.mm"
include "baibd.mm"
include "bitrd.mm"
include "biimpa.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wo.mm"
include "ffvelrnda.mm"
include "fvex.mm"
include "elpr.mm"
include "ord.mm"
include "sylibrd.mm"
include "con1d.mm"
include "imp.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "impbida.mm"
include "elpw2g.mm"
include "cbvmptv.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cvv.mm"
include "prex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "anbi1d.mm"

theorem pw2f1olem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume pw2f1o.1: |- ( ph -> A e. V )
  assume pw2f1o.2: |- ( ph -> B e. W )
  assume pw2f1o.3: |- ( ph -> C e. W )
  assume pw2f1o.4: |- ( ph -> B =/= C )

  disjoint A z
  disjoint B z
  disjoint C z
  disjoint S z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint G x
  disjoint G y
  assert |- ( ph -> ( ( S e. ~P A /\ G = ( z e. A |-> if ( z e. S , C , B ) ) ) <-> ( G e. ( { B , C } ^m A ) /\ S = ( `' G " { C } ) ) ) )

  proof
    wph
    cS
    cA
    wss
    #
    cG
    vy
    cA
    vy
    cv
    #
    cS
    wcel
    #
    cC
    cB
    cif
    #
    cmpt
    #
    wceq
    #
    wa
    #
    cA
    cB
    cC
    cpr
    #
    cG
    wf
    #
    cS
    cG
    ccnv
    cC
    csn
    #
    cima
    #
    wceq
    #
    wa
    #
    cS
    cA
    cpw
    wcel
    #
    cG
    vz
    cA
    vz
    cv
    #
    cS
    wcel
    #
    cC
    cB
    cif
    #
    cmpt
    #
    wceq
    #
    wa
    cG
    @7
    cA
    cmap
    co
    wcel
    #
    @11
    wa
    wph
    @6
    @12
    wph
    @6
    wa
    #
    @8
    @11
    @20
    @8
    cA
    @7
    @4
    wf
    #
    wph
    @21
    @6
    wph
    vy
    cA
    @3
    @7
    @4
    wph
    @3
    @7
    wcel
    @1
    cA
    wcel
    #
    wph
    @2
    cC
    cB
    @7
    wph
    cC
    cW
    wcel
    cC
    @7
    wcel
    pw2f1o.3
    cB
    cC
    cW
    prid2g
    syl
    #
    wph
    cB
    cW
    wcel
    cB
    @7
    wcel
    pw2f1o.2
    cB
    cC
    cW
    prid1g
    syl
    #
    ifcld
    adantr
    @4
    eqid
    #
    fmptd
    adantr
    @20
    cA
    @7
    cG
    @4
    wph
    @0
    @5
    simprr
    feq1d
    mpbird
    #
    @20
    vx
    cS
    @10
    @20
    vx
    cv
    #
    cA
    wcel
    #
    @27
    cS
    wcel
    #
    wa
    @28
    @27
    cG
    cfv
    #
    cC
    wceq
    #
    wa
    #
    @29
    @27
    @10
    wcel
    #
    @20
    @28
    @29
    @31
    @20
    @28
    wa
    #
    @29
    @29
    cC
    cB
    cif
    #
    cC
    wceq
    #
    @31
    @34
    @29
    @36
    @29
    cC
    cB
    iftrue
    @34
    @29
    @35
    cC
    @34
    @35
    cC
    wne
    @29
    wn
    #
    cB
    cC
    wne
    #
    wph
    @38
    @6
    @28
    pw2f1o.4
    ad2antrr
    @37
    @35
    cB
    cC
    @29
    cC
    cB
    iffalse
    neeq1d
    syl5ibrcom
    necon4bd
    impbid2
    @34
    @30
    @35
    cC
    @34
    @30
    @27
    @4
    cfv
    #
    @35
    @34
    @27
    cG
    @4
    wph
    @0
    @5
    @28
    simplrr
    fveq1d
    @28
    @28
    @35
    @7
    wcel
    #
    @39
    @35
    wceq
    @20
    @28
    id
    wph
    @40
    @6
    wph
    @29
    cC
    cB
    @7
    @23
    @24
    ifcld
    adantr
    vy
    @27
    @3
    @35
    cA
    @7
    @4
    @1
    @27
    wceq
    @2
    @29
    cC
    cB
    @1
    @27
    cS
    eleq1
    ifbid
    @25
    fvmptg
    syl2anr
    eqtrd
    eqeq1d
    bitr4d
    pm5.32da
    @20
    @29
    @28
    @20
    cS
    cA
    @27
    wph
    @0
    @5
    simprl
    sseld
    pm4.71rd
    @20
    cG
    cA
    wfn
    #
    @33
    @32
    wb
    @20
    @8
    @41
    @26
    cA
    @7
    cG
    ffn
    #
    syl
    cA
    cC
    @27
    cG
    fniniseg
    syl
    3bitr4d
    eqrdv
    jca
    wph
    @12
    wa
    #
    @0
    @5
    @43
    cS
    @10
    cA
    wph
    @8
    @11
    simprr
    @43
    cG
    cdm
    #
    @10
    cA
    cG
    @9
    cnvimass
    @8
    @44
    cA
    wceq
    wph
    @11
    cA
    @7
    cG
    fdm
    ad2antrl
    syl5sseq
    eqsstrd
    @43
    cG
    vy
    cA
    @1
    cG
    cfv
    #
    cmpt
    #
    @4
    @43
    @41
    cG
    @46
    wceq
    @8
    @41
    wph
    @11
    @42
    ad2antrl
    #
    vy
    cA
    cG
    dffn5
    sylib
    @43
    vy
    cA
    @45
    @3
    @43
    @22
    wa
    #
    @2
    @45
    @3
    wceq
    @48
    @2
    wa
    @45
    cC
    @3
    @48
    @2
    @45
    cC
    wceq
    #
    @48
    @2
    @1
    @10
    wcel
    #
    @49
    @48
    cS
    @10
    @1
    wph
    @8
    @11
    @22
    simplrr
    eleq2d
    @43
    @50
    @22
    @49
    @43
    @41
    @50
    @22
    @49
    wa
    wb
    @47
    cA
    cC
    @1
    cG
    fniniseg
    syl
    baibd
    bitrd
    #
    biimpa
    @2
    @3
    cC
    wceq
    @48
    @2
    cC
    cB
    iftrue
    adantl
    eqtr4d
    @48
    @2
    wn
    #
    wa
    @45
    cB
    @3
    @48
    @52
    @45
    cB
    wceq
    #
    @48
    @53
    @2
    @48
    @53
    wn
    @49
    @2
    @48
    @53
    @49
    @48
    @45
    @7
    wcel
    @53
    @49
    wo
    @43
    cA
    @7
    @1
    cG
    wph
    @8
    @11
    simprl
    ffvelrnda
    @45
    cB
    cC
    @1
    cG
    fvex
    elpr
    sylib
    ord
    @51
    sylibrd
    con1d
    imp
    @52
    @3
    cB
    wceq
    @48
    @2
    cC
    cB
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    mpteq2dva
    eqtrd
    jca
    impbida
    wph
    @13
    @0
    @18
    @5
    wph
    cA
    cV
    wcel
    #
    @13
    @0
    wb
    pw2f1o.1
    cS
    cA
    cV
    elpw2g
    syl
    wph
    @17
    @4
    cG
    @17
    @4
    wceq
    wph
    vz
    vy
    cA
    @16
    @3
    @14
    @1
    wceq
    @15
    @2
    cC
    cB
    @14
    @1
    cS
    eleq1
    ifbid
    cbvmptv
    a1i
    eqeq2d
    anbi12d
    wph
    @19
    @8
    @11
    wph
    @7
    cvv
    wcel
    @54
    @19
    @8
    wb
    cB
    cC
    prex
    pw2f1o.1
    @7
    cA
    cG
    cvv
    cV
    elmapg
    sylancr
    anbi1d
    3bitr4d
end
