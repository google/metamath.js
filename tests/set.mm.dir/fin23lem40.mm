include "cfin2.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "com.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "simpl.mm"
include "frn.mm"
include "ad2antrl.mm"
include "cdm.mm"
include "fdm.mm"
include "peano1.mm"
include "ne0i.mm"
include "mp1i.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "ccnv.mm"
include "wfn.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wpo.mm"
include "ffn.mm"
include "wpss.mm"
include "sspss.mm"
include "fvex.mm"
include "brcnv.mm"
include "brrpss.mm"
include "bitri.mm"
include "eqcom.mm"
include "orbi12i.mm"
include "sylbb2.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "porpss.mm"
include "cnvpo.mm"
include "mpbi.mm"
include "a1i.mm"
include "sornom.mm"
include "syl3anc.mm"
include "cnvso.mm"
include "sylibr.mm"
include "fin2i2.mm"
include "syl22anc.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "isfin3ds.mm"
include "mpbird.mm"

theorem fin23lem40
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume fin23lem40.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  disjoint a g
  disjoint a x
  disjoint A a
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint F a
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e x
  disjoint A e
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint F b
  disjoint F c
  disjoint F e
  assert |- ( A e. Fin2 -> A e. F )

  proof
    cA
    cfin2
    wcel
    #
    cA
    cF
    wcel
    vb
    cv
    #
    csuc
    #
    vf
    cv
    #
    cfv
    #
    @1
    @3
    cfv
    #
    wss
    #
    vb
    com
    wral
    #
    @3
    crn
    #
    cint
    @8
    wcel
    #
    wi
    #
    vf
    cA
    cpw
    #
    com
    cmap
    co
    #
    wral
    @0
    @10
    vf
    @12
    @3
    @12
    wcel
    @0
    com
    @11
    @3
    wf
    #
    @10
    @3
    @11
    com
    elmapi
    @0
    @13
    @7
    @9
    @0
    @13
    @7
    wa
    #
    wa
    #
    @0
    @8
    @11
    wss
    #
    @8
    c0
    wne
    #
    @8
    crpss
    wor
    #
    @9
    @0
    @14
    simpl
    @13
    @16
    @0
    @7
    com
    @11
    @3
    frn
    ad2antrl
    @13
    @17
    @0
    @7
    @13
    @3
    cdm
    #
    c0
    wne
    @17
    @13
    @19
    com
    c0
    com
    @11
    @3
    fdm
    c0
    com
    wcel
    com
    c0
    wne
    @13
    peano1
    com
    c0
    ne0i
    mp1i
    eqnetrd
    @19
    c0
    @8
    c0
    @3
    dm0rn0
    necon3bii
    sylib
    ad2antrl
    @15
    @8
    crpss
    ccnv
    #
    wor
    #
    @18
    @15
    @3
    com
    wfn
    #
    @5
    @4
    @20
    wbr
    #
    @5
    @4
    wceq
    #
    wo
    #
    vb
    com
    wral
    #
    @8
    @20
    wpo
    #
    @21
    @13
    @22
    @0
    @7
    com
    @11
    @3
    ffn
    ad2antrl
    @7
    @26
    @0
    @13
    @6
    @25
    vb
    com
    @6
    @4
    @5
    wpss
    #
    @4
    @5
    wceq
    #
    wo
    @25
    @4
    @5
    sspss
    @23
    @28
    @24
    @29
    @23
    @4
    @5
    crpss
    wbr
    @28
    @5
    @4
    crpss
    @1
    @3
    fvex
    #
    @2
    @3
    fvex
    brcnv
    @4
    @5
    @30
    brrpss
    bitri
    @5
    @4
    eqcom
    orbi12i
    sylbb2
    ralimi
    ad2antll
    @27
    @15
    @8
    crpss
    wpo
    @27
    @8
    porpss
    @8
    crpss
    cnvpo
    mpbi
    a1i
    @20
    @3
    vb
    sornom
    syl3anc
    @8
    crpss
    cnvso
    sylibr
    cA
    @8
    fin2i2
    syl22anc
    expr
    sylan2
    ralrimiva
    vb
    cA
    vf
    vg
    cF
    cfin2
    va
    vx
    fin23lem40.f
    isfin3ds
    mpbird
end
