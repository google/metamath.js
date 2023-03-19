include "con0.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cint.mm"
include "cmpt.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wfn.mm"
include "cvv.mm"
include "crn.mm"
include "cdif.mm"
include "tfr1.mm"
include "fndm.mm"
include "ax-mp.mm"
include "sseqtri.mm"
include "dnnumch2.mm"
include "sselda.mm"
include "inisegn0.mm"
include "sylib.mm"
include "oninton.mm"
include "sylancr.mm"
include "eqid.mm"
include "fmptd.mm"
include "dnnumch3lem.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqeq12d.mm"
include "fveq2.mm"
include "adantl.mm"
include "onint.mm"
include "wb.mm"
include "fniniseg.mm"
include "simprbi.mm"
include "syl.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem dnnumch3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  assume dnnumch.f: |- F = recs ( ( z e. _V |-> ( G ` ( A \ ran z ) ) ) )
  assume dnnumch.a: |- ( ph -> A e. V )
  assume dnnumch.g: |- ( ph -> A. y e. ~P A ( y =/= (/) -> ( G ` y ) e. y ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint F v
  disjoint F w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint G v
  disjoint G w
  disjoint v z
  disjoint w z
  disjoint A v
  disjoint A w
  disjoint ph v
  disjoint ph w
  assert |- ( ph -> ( x e. A |-> |^| ( `' F " { x } ) ) : A -1-1-> On )

  proof
    wph
    cA
    con0
    vx
    cA
    cF
    ccnv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    cint
    #
    cmpt
    #
    wf
    vv
    cv
    #
    @5
    cfv
    #
    vw
    cv
    #
    @5
    cfv
    #
    wceq
    #
    @6
    @8
    wceq
    #
    wi
    #
    vw
    cA
    wral
    vv
    cA
    wral
    cA
    con0
    @5
    wf1
    wph
    vx
    cA
    @4
    con0
    @5
    wph
    @1
    cA
    wcel
    wa
    #
    @3
    con0
    wss
    @3
    c0
    wne
    #
    @4
    con0
    wcel
    @3
    cF
    cdm
    #
    con0
    cF
    @2
    cnvimass
    cF
    con0
    wfn
    #
    @15
    con0
    wceq
    cF
    vz
    cvv
    cA
    vz
    cv
    crn
    cdif
    cG
    cfv
    cmpt
    dnnumch.f
    tfr1
    #
    con0
    cF
    fndm
    ax-mp
    #
    sseqtri
    @13
    @1
    cF
    crn
    #
    wcel
    @14
    wph
    cA
    @19
    @1
    wph
    vy
    vz
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch2
    #
    sselda
    @1
    cF
    inisegn0
    sylib
    @3
    oninton
    sylancr
    @5
    eqid
    fmptd
    wph
    @12
    vv
    vw
    cA
    cA
    wph
    @6
    cA
    wcel
    #
    @8
    cA
    wcel
    #
    wa
    wa
    #
    @10
    @0
    @6
    csn
    #
    cima
    #
    cint
    #
    @0
    @8
    csn
    #
    cima
    #
    cint
    #
    wceq
    #
    @11
    @23
    @7
    @26
    @9
    @29
    wph
    @21
    @7
    @26
    wceq
    @22
    wph
    vx
    vy
    vz
    vv
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch3lem
    adantrr
    wph
    @22
    @9
    @29
    wceq
    @21
    wph
    vx
    vy
    vz
    vw
    cA
    cF
    cG
    cV
    dnnumch.f
    dnnumch.a
    dnnumch.g
    dnnumch3lem
    adantrl
    eqeq12d
    @23
    @30
    @11
    @23
    @30
    wa
    @26
    cF
    cfv
    #
    @29
    cF
    cfv
    #
    @6
    @8
    @30
    @31
    @32
    wceq
    @23
    @26
    @29
    cF
    fveq2
    adantl
    @23
    @31
    @6
    wceq
    #
    @30
    wph
    @21
    @33
    @22
    wph
    @21
    wa
    #
    @26
    @25
    wcel
    #
    @33
    @34
    @25
    con0
    wss
    @25
    c0
    wne
    #
    @35
    @25
    @15
    con0
    cF
    @24
    cnvimass
    @18
    sseqtri
    @34
    @6
    @19
    wcel
    @36
    wph
    cA
    @19
    @6
    @20
    sselda
    @6
    cF
    inisegn0
    sylib
    @25
    onint
    sylancr
    @35
    @26
    con0
    wcel
    #
    @33
    @16
    @35
    @37
    @33
    wa
    wb
    @17
    con0
    @6
    @26
    cF
    fniniseg
    ax-mp
    simprbi
    syl
    adantrr
    adantr
    @23
    @32
    @8
    wceq
    #
    @30
    wph
    @22
    @38
    @21
    wph
    @22
    wa
    #
    @29
    @28
    wcel
    #
    @38
    @39
    @28
    con0
    wss
    @28
    c0
    wne
    #
    @40
    @28
    @15
    con0
    cF
    @27
    cnvimass
    @18
    sseqtri
    @39
    @8
    @19
    wcel
    @41
    wph
    cA
    @19
    @8
    @20
    sselda
    @8
    cF
    inisegn0
    sylib
    @28
    onint
    sylancr
    @40
    @29
    con0
    wcel
    #
    @38
    @16
    @40
    @42
    @38
    wa
    wb
    @17
    con0
    @8
    @29
    cF
    fniniseg
    ax-mp
    simprbi
    syl
    adantrl
    adantr
    3eqtr3d
    ex
    sylbid
    ralrimivva
    vv
    vw
    cA
    con0
    @5
    dff13
    sylanbrc
end
