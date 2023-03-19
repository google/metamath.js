include "clmod.mm"
include "wcel.mm"
include "cnzr.mm"
include "clindf.mm"
include "wbr.mm"
include "w3a.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "simp3.mm"
include "simp1.mm"
include "lindff.mm"
include "syl2anc.mm"
include "wa.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wn.mm"
include "wss.mm"
include "simpl1.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "adantr.mm"
include "eqid.mm"
include "lspssid.mm"
include "wfun.mm"
include "ffun.mm"
include "simprll.mm"
include "jca.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantlr.mm"
include "adantl.mm"
include "funfvima.mm"
include "sylc.mm"
include "sseldd.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprlr.mm"
include "lindfind2.mm"
include "syl211anc.mm"
include "nelne2.mm"
include "expr.mm"
include "necon4d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem lindff1
  let cB: class B
  let cF: class F
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume lindff1.b: |- B = ( Base ` W )
  assume lindff1.l: |- L = ( Scalar ` W )


  assert |- ( ( W e. LMod /\ L e. NzRing /\ F LIndF W ) -> F : dom F -1-1-> B )

  proof
    cW
    clmod
    wcel
    #
    cL
    cnzr
    wcel
    #
    cF
    cW
    clindf
    wbr
    #
    w3a
    #
    cF
    cdm
    #
    cB
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    vx
    vy
    weq
    wi
    #
    vy
    @4
    wral
    vx
    @4
    wral
    @4
    cB
    cF
    wf1
    @3
    @2
    @0
    @5
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp1
    cB
    cF
    cW
    clmod
    lindff1.b
    lindff
    syl2anc
    #
    @3
    @10
    vx
    vy
    @4
    @4
    @3
    @6
    @4
    wcel
    #
    @8
    @4
    wcel
    #
    wa
    #
    wa
    @6
    @8
    @7
    @9
    @3
    @14
    @6
    @8
    wne
    #
    @7
    @9
    wne
    #
    @3
    @14
    @15
    wa
    #
    wa
    #
    @7
    cF
    @4
    @8
    csn
    cdif
    #
    cima
    #
    cW
    clspn
    cfv
    #
    cfv
    #
    wcel
    @9
    @22
    wcel
    wn
    #
    @16
    @18
    @20
    @22
    @7
    @18
    @0
    @20
    cB
    wss
    #
    @20
    @22
    wss
    @0
    @1
    @2
    @17
    simpl1
    #
    @3
    @24
    @17
    @3
    @20
    cF
    crn
    #
    cB
    cF
    @19
    imassrn
    @3
    @5
    @26
    cB
    wss
    @11
    @4
    cB
    cF
    frn
    syl
    syl5ss
    adantr
    @20
    @21
    cB
    cW
    lindff1.b
    @21
    eqid
    #
    lspssid
    syl2anc
    @18
    cF
    wfun
    #
    @12
    wa
    @6
    @19
    wcel
    #
    @7
    @20
    wcel
    @18
    @28
    @12
    @3
    @28
    @17
    @3
    @5
    @28
    @11
    @4
    cB
    cF
    ffun
    syl
    adantr
    @3
    @12
    @13
    @15
    simprll
    jca
    @17
    @29
    @3
    @12
    @15
    @29
    @13
    @29
    @12
    @15
    wa
    @6
    @4
    @8
    eldifsn
    biimpri
    adantlr
    adantl
    @19
    @6
    cF
    funfvima
    sylc
    sseldd
    @18
    @0
    @1
    @2
    @13
    @23
    @25
    @0
    @1
    @2
    @17
    simpl2
    @0
    @1
    @2
    @17
    simpl3
    @3
    @12
    @13
    @15
    simprlr
    @8
    cF
    @21
    cL
    cW
    @27
    lindff1.l
    lindfind2
    syl211anc
    @7
    @9
    @22
    nelne2
    syl2anc
    expr
    necon4d
    ralrimivva
    vx
    vy
    @4
    cB
    cF
    dff13
    sylanbrc
end
