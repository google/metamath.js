include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cplusg.mm"
include "cmulr.mm"
include "cres.mm"
include "c0g.mm"
include "cabv.mm"
include "wceq.mm"
include "a1i.mm"
include "cbs.mm"
include "subrgbas.mm"
include "adantl.mm"
include "eqid.mm"
include "ressplusg.mm"
include "ressmulr.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subg0.mm"
include "syl.mm"
include "crg.mm"
include "subrgring.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "abvf.mm"
include "subrgss.mm"
include "fssres.mm"
include "syl2an.mm"
include "cc0.mm"
include "subg0cl.mm"
include "fvres.mm"
include "3syl.mm"
include "abv0.mm"
include "adantr.mm"
include "eqtrd.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "simp1l.mm"
include "sselda.mm"
include "3adant3.mm"
include "simp3.mm"
include "abvgt0.mm"
include "syl3anc.mm"
include "3ad2ant2.mm"
include "breqtrrd.mm"
include "co.mm"
include "cmul.mm"
include "simp1r.mm"
include "simp2l.mm"
include "sseldd.mm"
include "simp3l.mm"
include "abvmul.mm"
include "subrgmcl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "caddc.mm"
include "cle.mm"
include "abvtri.mm"
include "subrgacl.mm"
include "3brtr4d.mm"
include "isabvd.mm"

theorem abvres
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume abvres.a: |- A = ( AbsVal ` R )
  assume abvres.s: |- S = ( R |`s C )
  assume abvres.b: |- B = ( AbsVal ` S )


  assert |- ( ( F e. A /\ C e. ( SubRing ` R ) ) -> ( F |` C ) e. B )

  proof
    cF
    cA
    wcel
    #
    cC
    cR
    csubrg
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    cB
    cC
    cR
    cplusg
    cfv
    #
    cS
    cR
    cmulr
    cfv
    #
    cF
    cC
    cres
    #
    cR
    c0g
    cfv
    #
    cB
    cS
    cabv
    cfv
    wceq
    @3
    abvres.b
    a1i
    @2
    cC
    cS
    cbs
    cfv
    wceq
    @0
    cC
    cR
    cS
    abvres.s
    subrgbas
    adantl
    @2
    @4
    cS
    cplusg
    cfv
    wceq
    @0
    cC
    @4
    cR
    cS
    @1
    abvres.s
    @4
    eqid
    #
    ressplusg
    adantl
    @2
    @5
    cS
    cmulr
    cfv
    wceq
    @0
    cC
    cR
    cS
    @5
    @1
    abvres.s
    @5
    eqid
    #
    ressmulr
    adantl
    @3
    cC
    cR
    csubg
    cfv
    wcel
    #
    @7
    cS
    c0g
    cfv
    wceq
    @2
    @10
    @0
    cC
    cR
    subrgsubg
    adantl
    #
    cC
    cR
    cS
    @7
    abvres.s
    @7
    eqid
    #
    subg0
    syl
    @2
    cS
    crg
    wcel
    @0
    cC
    cR
    cS
    abvres.s
    subrgring
    adantl
    @0
    cR
    cbs
    cfv
    #
    cr
    cF
    wf
    cC
    @13
    wss
    #
    cC
    cr
    @6
    wf
    @2
    cA
    @13
    cR
    cF
    abvres.a
    @13
    eqid
    #
    abvf
    cC
    @13
    cR
    @15
    subrgss
    #
    @13
    cr
    cC
    cF
    fssres
    syl2an
    @3
    @7
    @6
    cfv
    #
    @7
    cF
    cfv
    #
    cc0
    @3
    @10
    @7
    cC
    wcel
    @17
    @18
    wceq
    @11
    cC
    cR
    @7
    @12
    subg0cl
    @7
    cC
    cF
    fvres
    3syl
    @0
    @18
    cc0
    wceq
    @2
    cA
    cR
    cF
    @7
    abvres.a
    @12
    abv0
    adantr
    eqtrd
    @3
    vx
    cv
    #
    cC
    wcel
    #
    @19
    @7
    wne
    #
    w3a
    #
    cc0
    @19
    cF
    cfv
    #
    @19
    @6
    cfv
    #
    clt
    @22
    @0
    @19
    @13
    wcel
    #
    @21
    cc0
    @23
    clt
    wbr
    @0
    @2
    @20
    @21
    simp1l
    @3
    @20
    @25
    @21
    @3
    cC
    @13
    @19
    @2
    @14
    @0
    @16
    adantl
    sselda
    3adant3
    @3
    @20
    @21
    simp3
    cA
    @13
    cR
    cF
    @19
    @7
    abvres.a
    @15
    @12
    abvgt0
    syl3anc
    @20
    @3
    @24
    @23
    wceq
    #
    @21
    @19
    cC
    cF
    fvres
    #
    3ad2ant2
    breqtrrd
    @3
    @20
    @21
    wa
    #
    vy
    cv
    #
    cC
    wcel
    #
    @29
    @7
    wne
    #
    wa
    #
    w3a
    #
    @19
    @29
    @5
    co
    #
    cF
    cfv
    #
    @23
    @29
    cF
    cfv
    #
    cmul
    co
    #
    @34
    @6
    cfv
    #
    @24
    @29
    @6
    cfv
    #
    cmul
    co
    @33
    @0
    @25
    @29
    @13
    wcel
    #
    @35
    @37
    wceq
    @0
    @2
    @28
    @32
    simp1l
    #
    @33
    cC
    @13
    @19
    @33
    @2
    @14
    @0
    @2
    @28
    @32
    simp1r
    #
    @16
    syl
    #
    @3
    @20
    @21
    @32
    simp2l
    #
    sseldd
    #
    @33
    cC
    @13
    @29
    @43
    @3
    @28
    @30
    @31
    simp3l
    #
    sseldd
    #
    cA
    @13
    cR
    @5
    cF
    @19
    @29
    abvres.a
    @15
    @9
    abvmul
    syl3anc
    @33
    @34
    cC
    wcel
    #
    @38
    @35
    wceq
    @33
    @2
    @20
    @30
    @48
    @42
    @44
    @46
    cC
    cR
    @5
    @19
    @29
    @9
    subrgmcl
    syl3anc
    @34
    cC
    cF
    fvres
    syl
    @33
    @24
    @23
    @39
    @36
    cmul
    @33
    @20
    @26
    @44
    @27
    syl
    #
    @33
    @30
    @39
    @36
    wceq
    @46
    @29
    cC
    cF
    fvres
    syl
    #
    oveq12d
    3eqtr4d
    @33
    @19
    @29
    @4
    co
    #
    cF
    cfv
    #
    @23
    @36
    caddc
    co
    #
    @51
    @6
    cfv
    #
    @24
    @39
    caddc
    co
    cle
    @33
    @0
    @25
    @40
    @52
    @53
    cle
    wbr
    @41
    @45
    @47
    cA
    @13
    @4
    cR
    cF
    @19
    @29
    abvres.a
    @15
    @8
    abvtri
    syl3anc
    @33
    @51
    cC
    wcel
    #
    @54
    @52
    wceq
    @33
    @2
    @20
    @30
    @55
    @42
    @44
    @46
    cC
    @4
    cR
    @19
    @29
    @8
    subrgacl
    syl3anc
    @51
    cC
    cF
    fvres
    syl
    @33
    @24
    @23
    @39
    @36
    caddc
    @49
    @50
    oveq12d
    3brtr4d
    isabvd
end
