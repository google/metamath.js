include "caddc.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "wrex.mm"
include "ccom.mm"
include "wi.mm"
include "wral.mm"
include "clt.mm"
include "cxr.mm"
include "wb.mm"
include "ressxr.mm"
include "abscld.mm"
include "sseldi.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "crab.mm"
include "csup.mm"
include "breq1i.mm"
include "wss.mm"
include "ssrab2.mm"
include "sstri.mm"
include "supxrleub.mm"
include "sylancr.mm"
include "syl5bb.mm"
include "weq.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "eleq1d.mm"
include "ralrab.mm"
include "syl6bb.mm"
include "mtbid.mm"
include "rexanali.mm"
include "sylibr.mm"
include "ltnle.mm"
include "sylan.mm"
include "adantr.mm"
include "cn0.mm"
include "cc.mm"
include "wf.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "recnd.mm"
include "simprr.mm"
include "0red.mm"
include "absge0d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "absidd.mm"
include "breqtrrd.mm"
include "simprl.mm"
include "radcnvlem1.mm"
include "radcnvlem2.mm"
include "jca.mm"
include "expr.mm"
include "sylbird.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem radcnvlt1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  let vk: setvar k
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cN: class N
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume radcnv.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume radcnvlt.x: |- ( ph -> X e. CC )
  assume radcnvlt.a: |- ( ph -> ( abs ` X ) < R )
  assume radcnvlt1.h: |- H = ( m e. NN0 |-> ( m x. ( abs ` ( ( G ` X ) ` m ) ) ) )

  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint H m
  disjoint m ph
  disjoint X m
  disjoint m r
  disjoint G m
  disjoint G r
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m s
  disjoint m y
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint r s
  disjoint r y
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ph -> ( seq 0 ( + , H ) e. dom ~~> /\ seq 0 ( + , ( abs o. ( G ` X ) ) ) e. dom ~~> ) )

  proof
    wph
    caddc
    vs
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    @0
    cX
    cabs
    cfv
    #
    cle
    wbr
    #
    wn
    #
    wa
    #
    vs
    cr
    wrex
    #
    caddc
    cH
    cc0
    cseq
    @3
    wcel
    #
    caddc
    cabs
    cX
    cG
    cfv
    ccom
    cc0
    cseq
    @3
    wcel
    #
    wa
    #
    wph
    @4
    @6
    wi
    vs
    cr
    wral
    #
    wn
    @9
    wph
    cR
    @5
    cle
    wbr
    #
    @13
    wph
    @5
    cR
    clt
    wbr
    #
    @14
    wn
    #
    radcnvlt.a
    wph
    @5
    cxr
    wcel
    #
    cR
    cxr
    wcel
    @15
    @16
    wb
    wph
    cr
    cxr
    @5
    ressxr
    wph
    cX
    radcnvlt.x
    abscld
    #
    sseldi
    #
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pser.g
    radcnv.a
    radcnv.r
    radcnvcl
    sseldi
    @5
    cR
    xrltnle
    syl2anc
    mpbid
    wph
    @14
    @6
    vs
    caddc
    vr
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    @3
    wcel
    #
    vr
    cr
    crab
    #
    wral
    #
    @13
    @14
    @24
    cxr
    clt
    csup
    #
    @5
    cle
    wbr
    #
    wph
    @25
    cR
    @26
    @5
    cle
    radcnv.r
    breq1i
    wph
    @24
    cxr
    wss
    @17
    @27
    @25
    wb
    @24
    cr
    cxr
    @23
    vr
    cr
    ssrab2
    ressxr
    sstri
    @19
    vs
    @24
    @5
    supxrleub
    sylancr
    syl5bb
    @23
    @4
    @6
    vs
    vr
    cr
    vr
    vs
    weq
    #
    @22
    @2
    @3
    @28
    @21
    @1
    caddc
    cc0
    @20
    @0
    cG
    fveq2
    seqeq3d
    eleq1d
    ralrab
    syl6bb
    mtbid
    @4
    @6
    vs
    cr
    rexanali
    sylibr
    wph
    @8
    @12
    vs
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @4
    @7
    @12
    @30
    @4
    wa
    @7
    @5
    @0
    clt
    wbr
    #
    @12
    @30
    @31
    @7
    wb
    #
    @4
    wph
    @5
    cr
    wcel
    @29
    @32
    @18
    @5
    @0
    ltnle
    sylan
    adantr
    @30
    @4
    @31
    @12
    @30
    @4
    @31
    wa
    #
    wa
    #
    @10
    @11
    @34
    vx
    cA
    vm
    vn
    cG
    cH
    cX
    @0
    pser.g
    wph
    cn0
    cc
    cA
    wf
    @29
    @33
    radcnv.a
    ad2antrr
    #
    wph
    cX
    cc
    wcel
    @29
    @33
    radcnvlt.x
    ad2antrr
    #
    @34
    @0
    wph
    @29
    @33
    simplr
    #
    recnd
    #
    @34
    @5
    @0
    @0
    cabs
    cfv
    clt
    @30
    @4
    @31
    simprr
    #
    @34
    @0
    @37
    @34
    cc0
    @0
    @34
    0red
    #
    @37
    @34
    cc0
    @5
    @0
    @40
    @34
    cX
    @36
    abscld
    @37
    @34
    cX
    @36
    absge0d
    @39
    lelttrd
    ltled
    absidd
    breqtrrd
    #
    @30
    @4
    @31
    simprl
    #
    radcnvlt1.h
    radcnvlem1
    @34
    vx
    cA
    vn
    cG
    cX
    @0
    pser.g
    @35
    @36
    @38
    @41
    @42
    radcnvlem2
    jca
    expr
    sylbird
    expimpd
    rexlimdva
    mpd
end
