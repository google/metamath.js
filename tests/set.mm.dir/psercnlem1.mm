include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "cif.mm"
include "cc.mm"
include "wss.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "abscld.mm"
include "readdcl.mm"
include "sylan.mm"
include "rehalfcld.mm"
include "wn.mm"
include "peano2re.mm"
include "syl.mm"
include "adantr.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "0re.mm"
include "absge0d.mm"
include "breq2.mm"
include "cle.mm"
include "w3a.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylib.mm"
include "simprd.mm"
include "cxr.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "sseldi.mm"
include "elico2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "avglt1.mm"
include "ltp1d.mm"
include "ifbothda.mm"
include "syl6breqr.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "breq1.mm"
include "avglt2.mm"
include "rexrd.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "cmnf.mm"
include "wi.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "simp2d.mm"
include "ge0gtmnf.mm"
include "xrre.mm"
include "expr.mm"
include "syl21anc.mm"
include "sylbird.mm"
include "con1d.mm"
include "imp.mm"
include "syl5eqbr.mm"
include "3jca.mm"

theorem psercnlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume psercn.s: |- S = ( `' abs " ( 0 [,) R ) )
  assume psercn.m: |- M = if ( R e. RR , ( ( ( abs ` a ) + R ) / 2 ) , ( ( abs ` a ) + 1 ) )

  disjoint a j
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M j
  disjoint M y
  disjoint G j
  disjoint G r
  disjoint G y
  disjoint S a
  disjoint S j
  disjoint S y
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint ph y
  disjoint a k
  disjoint a m
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint M i
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint M k
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint i x
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint i r
  disjoint G i
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S i
  disjoint S k
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint i ph
  disjoint k ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ( ph /\ a e. S ) -> ( M e. RR+ /\ ( abs ` a ) < M /\ M < R ) )

  proof
    wph
    va
    cv
    #
    cS
    wcel
    #
    wa
    #
    cM
    crp
    wcel
    @0
    cabs
    cfv
    #
    cM
    clt
    wbr
    cM
    cR
    clt
    wbr
    @2
    cM
    @2
    cM
    cR
    cr
    wcel
    #
    @3
    cR
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @3
    c1
    caddc
    co
    #
    cif
    #
    cr
    psercn.m
    @2
    @4
    @6
    @7
    cr
    @2
    @4
    wa
    #
    @5
    @2
    @3
    cr
    wcel
    #
    @4
    @5
    cr
    wcel
    @2
    @0
    wph
    cS
    cc
    @0
    cS
    cc
    wss
    wph
    cS
    cabs
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @12
    cabs
    cdm
    cc
    cabs
    @11
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    eqsstri
    a1i
    sselda
    #
    abscld
    #
    @3
    cR
    readdcl
    sylan
    rehalfcld
    @2
    @7
    cr
    wcel
    #
    @4
    wn
    #
    @2
    @10
    @15
    @14
    @3
    peano2re
    syl
    #
    adantr
    ifclda
    syl5eqel
    #
    @2
    cc0
    @3
    cM
    cc0
    cr
    wcel
    #
    @2
    0re
    a1i
    @14
    @18
    @2
    @0
    @13
    absge0d
    @2
    @3
    @8
    cM
    clt
    @4
    @3
    @6
    clt
    wbr
    #
    @3
    @7
    clt
    wbr
    #
    @3
    @8
    clt
    wbr
    @2
    @6
    @7
    @6
    @8
    @3
    clt
    breq2
    @7
    @8
    @3
    clt
    breq2
    @9
    @3
    cR
    clt
    wbr
    #
    @20
    @2
    @22
    @4
    @2
    @10
    cc0
    @3
    cle
    wbr
    #
    @22
    @2
    @3
    @11
    wcel
    #
    @10
    @23
    @22
    w3a
    #
    @2
    @0
    cc
    wcel
    #
    @24
    @2
    @0
    @12
    wcel
    #
    @26
    @24
    wa
    #
    @2
    @0
    cS
    @12
    wph
    @1
    simpr
    psercn.s
    syl6eleq
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @27
    @28
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @0
    @11
    cabs
    elpreima
    mp2b
    sylib
    simprd
    @2
    @19
    cR
    cxr
    wcel
    #
    @24
    @25
    wb
    0re
    @2
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    cR
    @30
    wcel
    #
    @1
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pserf.g
    pserf.a
    pserf.r
    radcnvcl
    #
    adantr
    sseldi
    #
    cc0
    cR
    @3
    elico2
    sylancr
    mpbid
    simp3d
    adantr
    #
    @2
    @10
    @4
    @22
    @20
    wb
    @14
    @3
    cR
    avglt1
    sylan
    mpbid
    @2
    @21
    @16
    @2
    @3
    @14
    ltp1d
    adantr
    ifbothda
    psercn.m
    syl6breqr
    #
    lelttrd
    elrpd
    @35
    @2
    cM
    @8
    cR
    clt
    psercn.m
    @4
    @6
    cR
    clt
    wbr
    #
    @7
    cR
    clt
    wbr
    #
    @8
    cR
    clt
    wbr
    @2
    @6
    @7
    @6
    @8
    cR
    clt
    breq1
    @7
    @8
    cR
    clt
    breq1
    @9
    @22
    @36
    @34
    @2
    @10
    @4
    @22
    @36
    wb
    @14
    @3
    cR
    avglt2
    sylan
    mpbid
    @2
    @16
    @37
    @2
    @37
    @4
    @2
    @37
    wn
    #
    cR
    @7
    cle
    wbr
    #
    @4
    @2
    @29
    @7
    cxr
    wcel
    @39
    @38
    wb
    @33
    @2
    @7
    @17
    rexrd
    cR
    @7
    xrlenlt
    syl2anc
    @2
    @29
    @15
    cmnf
    cR
    clt
    wbr
    #
    @39
    @4
    wi
    @33
    @17
    @2
    @29
    cc0
    cR
    cle
    wbr
    #
    @40
    @33
    wph
    @41
    @1
    wph
    @29
    @41
    cR
    cpnf
    cle
    wbr
    #
    wph
    @31
    @29
    @41
    @42
    w3a
    #
    @32
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @31
    @43
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cR
    elicc1
    mp2an
    sylib
    simp2d
    adantr
    cR
    ge0gtmnf
    syl2anc
    @29
    @15
    wa
    @40
    @39
    @4
    cR
    @7
    xrre
    expr
    syl21anc
    sylbird
    con1d
    imp
    ifbothda
    syl5eqbr
    3jca
end
