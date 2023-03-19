include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cdm.mm"
include "wi.mm"
include "brovpreldm.mm"
include "copab.mm"
include "cmpt2.mm"
include "cv.mm"
include "wceq.mm"
include "simpl.mm"
include "opabbidv.mm"
include "mpt2eq123dv.mm"
include "ovmpt2ga.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "coprab.mm"
include "cxp.mm"
include "dmoprabss.mm"
include "sseli.mm"
include "opelxp.mm"
include "df-br.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "breqd.mm"
include "brabv.mm"
include "anim2i.mm"
include "ex.mm"
include "adantr.mm"
include "sylbid.mm"
include "com23.mm"
include "a1d.mm"
include "wn.mm"
include "mpt2ndm0.mm"
include "cfv.mm"
include "df-ov.mm"
include "fveq1.mm"
include "syl5eq.mm"
include "0fv.mm"
include "syl6eq.mm"
include "eqneqall.mm"
include "3syl.mm"
include "pm2.61i.mm"
include "syl.mm"
include "sylbi.mm"
include "pm2.43i.mm"
include "com12.mm"
include "anc2ri.mm"
include "df-3an.mm"
include "syl6ibr.mm"
include "df-mpt2.mm"
include "dmeqi.mm"
include "eleq2s.mm"
include "syl6bi.mm"
include "w3o.mm"
include "3ianor.mm"
include "wo.mm"
include "df-3or.mm"
include "ianor.mm"
include "dm0.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "noel.mm"
include "pm2.21i.mm"
include "sylbir.mm"
include "anor.mm"
include "id.mm"
include "ancri.mm"
include "mpt2exga.mm"
include "pm2.24d.mm"
include "imp.mm"
include "jaoi3.mm"

theorem bropopvvv
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cP: class P
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cO: class O
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume bropopvvv.o: |- O = ( v e. _V , e e. _V |-> ( a e. v , b e. v |-> { <. f , p >. | ph } ) )
  assume bropopvvv.p: |- ( ( v = V /\ e = E ) -> ( ph <-> ps ) )
  assume bropopvvv.oo: |- ( ( ( V e. _V /\ E e. _V ) /\ ( A e. V /\ B e. V ) ) -> ( A ( V O E ) B ) = { <. f , p >. | th } )

  disjoint E a
  disjoint E b
  disjoint E e
  disjoint E f
  disjoint E p
  disjoint E v
  disjoint a b
  disjoint a e
  disjoint a f
  disjoint a p
  disjoint a v
  disjoint b e
  disjoint b f
  disjoint b p
  disjoint b v
  disjoint e f
  disjoint e p
  disjoint e v
  disjoint f p
  disjoint f v
  disjoint p v
  disjoint V a
  disjoint V b
  disjoint V e
  disjoint V f
  disjoint V p
  disjoint V v
  disjoint e ps
  disjoint ps v
  disjoint V c
  disjoint a c
  disjoint b c
  disjoint c e
  disjoint c f
  disjoint c p
  disjoint c v
  disjoint c ps
  assert |- ( F ( A ( V O E ) B ) P -> ( ( V e. _V /\ E e. _V ) /\ ( F e. _V /\ P e. _V ) /\ ( A e. V /\ B e. V ) ) )

  proof
    cF
    cP
    cA
    cB
    cV
    cE
    cO
    co
    #
    co
    #
    wbr
    #
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    wa
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    w3a
    #
    @2
    cA
    cB
    cop
    #
    @0
    cdm
    #
    wcel
    #
    @2
    @8
    wi
    #
    @0
    cA
    cB
    cF
    cP
    brovpreldm
    @3
    @4
    va
    vb
    cV
    cV
    wps
    vf
    vp
    copab
    #
    cmpt2
    #
    cvv
    wcel
    #
    w3a
    #
    @11
    @12
    wi
    #
    @16
    @11
    @9
    @14
    cdm
    #
    wcel
    @12
    @16
    @10
    @18
    @9
    @16
    @0
    @14
    vv
    ve
    cV
    cE
    cvv
    cvv
    va
    vb
    vv
    cv
    #
    @19
    wph
    vf
    vp
    copab
    #
    cmpt2
    #
    @14
    cO
    cvv
    @19
    cV
    wceq
    #
    ve
    cv
    cE
    wceq
    #
    wa
    #
    va
    vb
    @19
    @19
    @20
    cV
    cV
    @13
    @22
    @23
    simpl
    #
    @25
    @24
    wph
    wps
    vf
    vp
    bropopvvv.p
    opabbidv
    mpt2eq123dv
    bropopvvv.o
    ovmpt2ga
    dmeqd
    eleq2d
    @12
    @9
    va
    cv
    cV
    wcel
    vb
    cv
    cV
    wcel
    wa
    vc
    cv
    @13
    wceq
    #
    wa
    va
    vb
    vc
    coprab
    #
    cdm
    #
    @18
    @9
    @28
    wcel
    @9
    cV
    cV
    cxp
    #
    wcel
    #
    @12
    @28
    @29
    @9
    @26
    va
    vb
    vc
    cV
    cV
    dmoprabss
    sseli
    @30
    @7
    @12
    cA
    cB
    cV
    cV
    opelxp
    @7
    @2
    @5
    @6
    wa
    #
    @7
    wa
    @8
    @7
    @2
    @31
    @2
    @7
    @31
    @2
    @7
    @31
    wi
    #
    @2
    cF
    cP
    cop
    #
    @1
    wcel
    #
    @2
    @32
    wi
    #
    cF
    cP
    @1
    df-br
    @34
    @1
    c0
    wne
    #
    @35
    @1
    @33
    ne0i
    @5
    @36
    @35
    wi
    #
    @5
    @35
    @36
    @5
    @7
    @2
    @31
    @5
    @7
    @2
    @31
    wi
    @5
    @7
    wa
    #
    @2
    cF
    cP
    wth
    vf
    vp
    copab
    #
    wbr
    #
    @31
    @38
    @1
    @39
    cF
    cP
    bropopvvv.oo
    breqd
    @5
    @40
    @31
    wi
    @7
    @5
    @40
    @31
    @40
    @6
    @5
    wth
    vf
    vp
    cF
    cP
    brabv
    anim2i
    ex
    adantr
    sylbid
    ex
    com23
    a1d
    @5
    wn
    #
    @0
    c0
    wceq
    #
    @1
    c0
    wceq
    @37
    vv
    ve
    @21
    cO
    cV
    cE
    cvv
    cvv
    bropopvvv.o
    mpt2ndm0
    #
    @42
    @1
    @9
    c0
    cfv
    #
    c0
    @42
    @1
    @9
    @0
    cfv
    @44
    cA
    cB
    @0
    df-ov
    @9
    @0
    c0
    fveq1
    syl5eq
    @9
    0fv
    syl6eq
    @35
    @1
    c0
    eqneqall
    3syl
    pm2.61i
    syl
    sylbi
    pm2.43i
    com12
    anc2ri
    @5
    @6
    @7
    df-3an
    syl6ibr
    sylbi
    syl
    @14
    @27
    va
    vb
    vc
    cV
    cV
    @13
    df-mpt2
    dmeqi
    eleq2s
    syl6bi
    @16
    wn
    @3
    wn
    #
    @4
    wn
    #
    @15
    wn
    #
    w3o
    #
    @17
    @3
    @4
    @15
    3ianor
    @48
    @45
    @46
    wo
    #
    @47
    wo
    @17
    @45
    @46
    @47
    df-3or
    @49
    @17
    @47
    @49
    @41
    @17
    @3
    @4
    ianor
    @41
    @11
    @9
    c0
    wcel
    #
    @12
    @41
    @11
    @9
    c0
    cdm
    #
    wcel
    @50
    @41
    @10
    @51
    @9
    @41
    @0
    c0
    @43
    dmeqd
    eleq2d
    @51
    c0
    @9
    dm0
    eleq2i
    syl6bb
    @50
    @12
    @9
    noel
    pm2.21i
    syl6bi
    sylbir
    @49
    wn
    #
    @47
    @17
    @52
    @5
    @47
    @17
    wi
    @3
    @4
    anor
    @5
    @15
    @17
    @5
    @3
    @3
    wa
    #
    @15
    @3
    @53
    @4
    @3
    @3
    @3
    id
    ancri
    adantr
    va
    vb
    cV
    cV
    @13
    cvv
    cvv
    mpt2exga
    syl
    pm2.24d
    sylbir
    imp
    jaoi3
    sylbi
    sylbi
    pm2.61i
    syl
    pm2.43i
end
