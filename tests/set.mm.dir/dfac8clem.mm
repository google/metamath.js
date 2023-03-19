include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "wwe.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wa.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wbr.mm"
include "wn.mm"
include "crio.mm"
include "eldifsn.mm"
include "wss.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "wreu.mm"
include "wse.mm"
include "simplr.mm"
include "vex.mm"
include "exse2.mm"
include "mp1i.mm"
include "simprr.mm"
include "wereu2.mm"
include "syl22anc.mm"
include "riotacl.mm"
include "syl.mm"
include "sseldd.mm"
include "sylan2b.mm"
include "fmptd.mm"
include "difexg.mm"
include "adantr.mm"
include "uniexg.mm"
include "fex2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "riotaex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylbir.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfim.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "spcegv.mm"
include "sylc.mm"
include "ex.mm"
include "exlimdv.mm"

theorem dfac8clem
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume dfac8clem.1: |- F = ( s e. ( A \ { (/) } ) |-> ( iota_ a e. s A. b e. s -. b r a ) )

  disjoint a b
  disjoint a f
  disjoint a r
  disjoint a s
  disjoint a z
  disjoint A a
  disjoint b f
  disjoint b r
  disjoint b s
  disjoint b z
  disjoint A b
  disjoint f r
  disjoint f s
  disjoint f z
  disjoint A f
  disjoint r s
  disjoint r z
  disjoint A r
  disjoint s z
  disjoint A s
  disjoint A z
  disjoint B r
  disjoint B s
  disjoint F f
  disjoint F z
  assert |- ( A e. B -> ( E. r r We U. A -> E. f A. z e. A ( z =/= (/) -> ( f ` z ) e. z ) ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cuni
    #
    vr
    cv
    #
    wwe
    #
    vz
    cv
    #
    c0
    wne
    #
    @4
    vf
    cv
    #
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vz
    cA
    wral
    #
    vf
    wex
    #
    vr
    @0
    @3
    @11
    @0
    @3
    wa
    #
    cF
    cvv
    wcel
    #
    @5
    @4
    cF
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vz
    cA
    wral
    #
    @11
    @12
    cA
    c0
    csn
    #
    cdif
    #
    @1
    cF
    wf
    @19
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @13
    @12
    vs
    @19
    vb
    cv
    va
    cv
    @2
    wbr
    wn
    vb
    vs
    cv
    #
    wral
    #
    va
    @22
    crio
    #
    @1
    cF
    @22
    @19
    wcel
    #
    @12
    @22
    cA
    wcel
    #
    @22
    c0
    wne
    #
    wa
    #
    @24
    @1
    wcel
    @22
    cA
    c0
    eldifsn
    #
    @12
    @28
    wa
    #
    @22
    @1
    @24
    @26
    @22
    @1
    wss
    #
    @12
    @27
    @22
    cA
    elssuni
    ad2antrl
    #
    @30
    @23
    va
    @22
    wreu
    #
    @24
    @22
    wcel
    @30
    @3
    @1
    @2
    wse
    #
    @31
    @27
    @33
    @0
    @3
    @28
    simplr
    @2
    cvv
    wcel
    @34
    @30
    vr
    vex
    @1
    @2
    cvv
    exse2
    mp1i
    @32
    @12
    @26
    @27
    simprr
    va
    vb
    @1
    @22
    @2
    wereu2
    syl22anc
    @23
    va
    @22
    riotacl
    syl
    #
    sseldd
    sylan2b
    dfac8clem.1
    fmptd
    @0
    @20
    @3
    cA
    @18
    cB
    difexg
    adantr
    @0
    @21
    @3
    cA
    cB
    uniexg
    adantr
    @19
    @1
    cF
    cvv
    cvv
    fex2
    syl3anc
    @12
    @27
    @22
    cF
    cfv
    #
    @22
    wcel
    #
    wi
    #
    vs
    cA
    wral
    @17
    @12
    @38
    vs
    cA
    @12
    @26
    @27
    @37
    @30
    @36
    @24
    @22
    @28
    @36
    @24
    wceq
    #
    @12
    @28
    @25
    @39
    @29
    @25
    @24
    cvv
    wcel
    @39
    @23
    va
    @22
    riotaex
    vs
    @19
    @24
    cvv
    cF
    dfac8clem.1
    fvmpt2
    mpan2
    sylbir
    adantl
    @35
    eqeltrd
    expr
    ralrimiva
    @16
    @38
    vz
    vs
    cA
    @5
    @15
    vs
    @5
    vs
    nfv
    vs
    @14
    @4
    vs
    @4
    cF
    vs
    cF
    vs
    @19
    @24
    cmpt
    dfac8clem.1
    vs
    @19
    @24
    nfmpt1
    nfcxfr
    vs
    @4
    nfcv
    nffv
    nfel1
    nfim
    @38
    vz
    nfv
    @4
    @22
    wceq
    #
    @5
    @27
    @15
    @37
    @4
    @22
    c0
    neeq1
    @40
    @14
    @36
    @4
    @22
    @4
    @22
    cF
    fveq2
    @40
    id
    eleq12d
    imbi12d
    cbvral
    sylibr
    @10
    @17
    vf
    cF
    cvv
    @6
    cF
    wceq
    #
    @9
    @16
    vz
    cA
    @41
    @8
    @15
    @5
    @41
    @7
    @14
    @4
    @4
    @6
    cF
    fveq1
    eleq1d
    imbi2d
    ralbidv
    spcegv
    sylc
    ex
    exlimdv
end
