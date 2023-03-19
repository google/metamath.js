include "cprime.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wrmo.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "simp-8l.mm"
include "simp-8r.mm"
include "simpllr.mm"
include "simp-7r.mm"
include "simp-6r.mm"
include "simplr.mm"
include "simp-5r.mm"
include "simpr.mm"
include "simp-4r.mm"
include "2sqmod.mm"
include "simpld.mm"
include "anasss.mm"
include "adantl5r.mm"
include "r19.29af.mm"
include "r19.29an.mm"
include "expl.mm"
include "ralrimiva.mm"
include "breq12.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cbvrexdva.mm"
include "rmo4.mm"
include "sylibr.mm"

theorem 2sqmo
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint P a
  disjoint P b
  disjoint a b
  disjoint P c
  disjoint P d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  assert |- ( P e. Prime -> E* a e. NN0 E. b e. NN0 ( a <_ b /\ ( ( a ^ 2 ) + ( b ^ 2 ) ) = P ) )

  proof
    cP
    cprime
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cle
    wbr
    #
    @1
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    caddc
    co
    #
    cP
    wceq
    #
    wa
    #
    vb
    cn0
    wrex
    #
    vc
    cv
    #
    vd
    cv
    #
    cle
    wbr
    #
    @10
    c2
    cexp
    co
    #
    @11
    c2
    cexp
    co
    #
    caddc
    co
    #
    cP
    wceq
    #
    wa
    #
    vd
    cn0
    wrex
    #
    wa
    @1
    @10
    wceq
    #
    wi
    #
    vc
    cn0
    wral
    #
    va
    cn0
    wral
    @9
    va
    cn0
    wrmo
    @0
    @21
    va
    cn0
    @0
    @1
    cn0
    wcel
    #
    wa
    #
    @20
    vc
    cn0
    @23
    @10
    cn0
    wcel
    #
    wa
    #
    @9
    @18
    @19
    @25
    @9
    wa
    #
    @17
    @19
    vd
    cn0
    @26
    @11
    cn0
    wcel
    #
    wa
    #
    @12
    @16
    @19
    @28
    @12
    wa
    #
    @16
    wa
    @8
    @19
    vb
    cn0
    @29
    @16
    vb
    @28
    @12
    vb
    @26
    @27
    vb
    @25
    @9
    vb
    @25
    vb
    nfv
    @8
    vb
    cn0
    nfre1
    nfan
    @27
    vb
    nfv
    nfan
    @12
    vb
    nfv
    nfan
    @16
    vb
    nfv
    nfan
    @25
    @9
    @27
    @12
    @16
    @2
    cn0
    wcel
    #
    @8
    @19
    @25
    @27
    wa
    #
    @12
    wa
    #
    @16
    wa
    #
    @30
    wa
    #
    @3
    @7
    @19
    @34
    @3
    wa
    #
    @7
    wa
    #
    @19
    @2
    @11
    wceq
    #
    @36
    @1
    @2
    @10
    @11
    cP
    @0
    @22
    @24
    @27
    @12
    @16
    @30
    @3
    @7
    simp-8l
    @0
    @22
    @24
    @27
    @12
    @16
    @30
    @3
    @7
    simp-8r
    @33
    @30
    @3
    @7
    simpllr
    @23
    @24
    @27
    @12
    @16
    @30
    @3
    @7
    simp-7r
    @25
    @27
    @12
    @16
    @30
    @3
    @7
    simp-6r
    @34
    @3
    @7
    simplr
    @31
    @12
    @16
    @30
    @3
    @7
    simp-5r
    @35
    @7
    simpr
    @32
    @16
    @30
    @3
    @7
    simp-4r
    2sqmod
    simpld
    anasss
    adantl5r
    @25
    @9
    @27
    @12
    @16
    simp-4r
    r19.29af
    anasss
    r19.29an
    expl
    ralrimiva
    ralrimiva
    @9
    @18
    va
    vc
    cn0
    @19
    @8
    @17
    vb
    vd
    cn0
    @19
    @37
    wa
    #
    @3
    @12
    @7
    @16
    @1
    @10
    @2
    @11
    cle
    breq12
    @38
    @6
    @15
    cP
    @38
    @4
    @13
    @5
    @14
    caddc
    @38
    @1
    @10
    c2
    cexp
    @19
    @37
    simpl
    oveq1d
    @38
    @2
    @11
    c2
    cexp
    @19
    @37
    simpr
    oveq1d
    oveq12d
    eqeq1d
    anbi12d
    cbvrexdva
    rmo4
    sylibr
end
