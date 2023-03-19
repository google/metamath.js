include "cdm.mm"
include "wf1.mm"
include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "clsw.mm"
include "crn.mm"
include "cmin.mm"
include "clt.mm"
include "ccnv.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "wi.mm"
include "eqid.mm"
include "clwlkclwwlklem2a.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "imbi2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "spcimedv.mm"

theorem clwlkclwwlklem1
  let cP: class P
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let cE: class E
  let cV: class V
  let vx: setvar x

  disjoint E f
  disjoint E i
  disjoint f i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint V f
  disjoint V i
  disjoint E x
  disjoint f x
  disjoint i x
  disjoint P x
  disjoint R x
  disjoint V x
  assert |- ( ( E : dom E -1-1-> R /\ P e. Word V /\ 2 <_ ( # ` P ) ) -> ( ( ( lastS ` P ) = ( P ` 0 ) /\ ( A. i e. ( 0 ..^ ( ( ( ( # ` P ) - 1 ) - 0 ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E /\ { ( P ` ( ( # ` P ) - 2 ) ) , ( P ` 0 ) } e. ran E ) ) -> E. f ( ( f e. Word dom E /\ P : ( 0 ... ( # ` f ) ) --> V /\ A. i e. ( 0 ..^ ( # ` f ) ) ( E ` ( f ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) /\ ( P ` 0 ) = ( P ` ( # ` f ) ) ) ) )

  proof
    cE
    cdm
    #
    cR
    cE
    wf1
    cP
    cV
    cword
    wcel
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    w3a
    #
    vf
    cv
    #
    @0
    cword
    #
    wcel
    #
    cc0
    @3
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    vi
    cv
    #
    @3
    cfv
    #
    cE
    cfv
    #
    @9
    cP
    cfv
    @9
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    wceq
    #
    vi
    cc0
    @6
    cfzo
    co
    #
    wral
    #
    w3a
    #
    cc0
    cP
    cfv
    #
    @6
    cP
    cfv
    #
    wceq
    #
    wa
    #
    cP
    clsw
    cfv
    @17
    wceq
    @12
    cE
    crn
    #
    wcel
    vi
    cc0
    @1
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    c1
    cmin
    co
    cfzo
    co
    wral
    @1
    c2
    cmin
    co
    #
    cP
    cfv
    @17
    cpr
    @21
    wcel
    wa
    wa
    #
    vf
    vx
    cc0
    @22
    cfzo
    co
    #
    vx
    cv
    #
    @23
    clt
    wbr
    @26
    cP
    cfv
    #
    @26
    c1
    caddc
    co
    cP
    cfv
    cpr
    cE
    ccnv
    #
    cfv
    @27
    @17
    cpr
    @28
    cfv
    cif
    #
    cmpt
    #
    cvv
    @25
    cvv
    wcel
    @30
    cvv
    wcel
    @2
    cc0
    @22
    cfzo
    ovex
    vx
    @25
    @29
    cvv
    mptexg
    mp1i
    @2
    @3
    @30
    wceq
    #
    wa
    @24
    @20
    wi
    #
    @24
    @30
    @4
    wcel
    #
    cc0
    @30
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    @9
    @30
    cfv
    #
    cE
    cfv
    #
    @12
    wceq
    #
    vi
    cc0
    @34
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @17
    @34
    cP
    cfv
    #
    wceq
    #
    wa
    #
    wi
    #
    @2
    @46
    @31
    vx
    cP
    cR
    vi
    cE
    @30
    cV
    @30
    eqid
    clwlkclwwlklem2a
    adantr
    @31
    @32
    @46
    wb
    @2
    @31
    @20
    @45
    @24
    @31
    @16
    @42
    @19
    @44
    @31
    @5
    @33
    @8
    @36
    @15
    @41
    @3
    @30
    @4
    eleq1
    @31
    @7
    @35
    cV
    cP
    @31
    @6
    @34
    cc0
    cfz
    @3
    @30
    chash
    fveq2
    #
    oveq2d
    feq2d
    @31
    @13
    @39
    vi
    @14
    @40
    @31
    @6
    @34
    cc0
    cfzo
    @47
    oveq2d
    @31
    @11
    @38
    @12
    @31
    @10
    @37
    cE
    @9
    @3
    @30
    fveq1
    fveq2d
    eqeq1d
    raleqbidv
    3anbi123d
    @31
    @18
    @43
    @17
    @31
    @6
    @34
    cP
    @47
    fveq2d
    eqeq2d
    anbi12d
    imbi2d
    adantl
    mpbird
    spcimedv
end
