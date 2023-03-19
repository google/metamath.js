include "wa.mm"
include "com.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "ccnv.mm"
include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "cpw.mm"
include "wf1.mm"
include "wf.mm"
include "adantr.mm"
include "f1f.mm"
include "syl.mm"
include "wss.mm"
include "ssrab2.mm"
include "cxp.mm"
include "wwe.mm"
include "w3a.mm"
include "cdom.mm"
include "wbr.mm"
include "simprl1.mm"
include "sylan2b.mm"
include "syl5ss.mm"
include "vex.mm"
include "rabex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "wb.mm"
include "pm5.19.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "wf1o.mm"
include "wceq.mm"
include "f1f1orn.mm"
include "f1ocnvfv1.mm"
include "wfn.mm"
include "f1fn.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "id.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "anass.mm"
include "bitr4i.mm"
include "baib.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "ex.mm"
include "mtoi.mm"
include "eldifd.mm"

theorem pwfseqlem1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cD: class D
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vz: setvar z
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vv: setvar v
  let cF: class F
  let cR: class R
  let cW: class W
  let cZ: class Z
  let cY: class Y
  assume pwfseqlem4.g: |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) )
  assume pwfseqlem4.x: |- ( ph -> X C_ A )
  assume pwfseqlem4.h: |- ( ph -> H : _om -1-1-onto-> X )
  assume pwfseqlem4.ps: |- ( ps <-> ( ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) /\ _om ~<_ x ) )
  assume pwfseqlem4.k: |- ( ( ph /\ ps ) -> K : U_ n e. _om ( x ^m n ) -1-1-> x )
  assume pwfseqlem4.d: |- D = ( G ` { w e. x | ( ( `' K ` w ) e. ran G /\ -. w e. ( `' G ` ( `' K ` w ) ) ) } )

  disjoint n r
  disjoint n w
  disjoint n x
  disjoint r w
  disjoint r x
  disjoint w x
  disjoint D n
  disjoint G w
  disjoint K w
  disjoint H r
  disjoint H x
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint n ps
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint n z
  disjoint r z
  disjoint w z
  disjoint x z
  disjoint n y
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint a b
  disjoint a s
  disjoint a v
  disjoint a y
  disjoint F a
  disjoint b s
  disjoint b v
  disjoint b y
  disjoint F b
  disjoint s v
  disjoint s y
  disjoint F s
  disjoint v y
  disjoint F v
  disjoint F y
  disjoint w y
  disjoint G y
  disjoint K y
  disjoint a r
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint b r
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint r s
  disjoint r v
  disjoint r y
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint x y
  disjoint H y
  disjoint H z
  disjoint a n
  disjoint a ph
  disjoint b n
  disjoint b ph
  disjoint n s
  disjoint n v
  disjoint ph s
  disjoint ph v
  disjoint ph z
  disjoint ps z
  disjoint R s
  disjoint A a
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint W a
  disjoint W b
  disjoint W s
  disjoint W v
  disjoint Z a
  disjoint Z b
  disjoint Z s
  disjoint Z v
  disjoint Y a
  disjoint Y s
  assert |- ( ( ph /\ ps ) -> D e. ( U_ n e. _om ( A ^m n ) \ U_ n e. _om ( x ^m n ) ) )

  proof
    wph
    wps
    wa
    #
    cD
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    ciun
    #
    vn
    com
    vx
    cv
    #
    @1
    cmap
    co
    ciun
    #
    @0
    cD
    vw
    cv
    #
    cK
    ccnv
    #
    cfv
    #
    cG
    crn
    #
    wcel
    #
    @5
    @7
    cG
    ccnv
    #
    cfv
    #
    wcel
    #
    wn
    #
    wa
    #
    vw
    @3
    crab
    #
    cG
    cfv
    #
    @2
    pwfseqlem4.d
    @0
    cA
    cpw
    #
    @2
    @15
    cG
    @0
    @17
    @2
    cG
    wf1
    #
    @17
    @2
    cG
    wf
    wph
    @18
    wps
    pwfseqlem4.g
    adantr
    #
    @17
    @2
    cG
    f1f
    syl
    @0
    @15
    cA
    wss
    @15
    @17
    wcel
    #
    @0
    @15
    @3
    cA
    @14
    vw
    @3
    ssrab2
    wps
    wph
    @3
    cA
    wss
    #
    vr
    cv
    #
    @3
    @3
    cxp
    wss
    #
    @3
    @22
    wwe
    #
    w3a
    com
    @3
    cdom
    wbr
    #
    wa
    @21
    pwfseqlem4.ps
    @21
    @23
    @24
    @25
    wph
    simprl1
    sylan2b
    syl5ss
    @15
    cA
    @14
    vw
    @3
    vx
    vex
    rabex
    elpw
    sylibr
    #
    ffvelrnd
    syl5eqel
    @0
    cD
    @4
    wcel
    #
    cD
    cK
    cfv
    #
    @15
    wcel
    #
    @29
    wn
    #
    wb
    #
    @29
    pm5.19
    @0
    @27
    @31
    @0
    @27
    wa
    #
    @29
    @28
    @28
    @6
    cfv
    #
    @10
    cfv
    #
    wcel
    #
    wn
    #
    @30
    @32
    @28
    @3
    wcel
    #
    @33
    @8
    wcel
    #
    @29
    @36
    wb
    @0
    @27
    @4
    @3
    cK
    wf
    #
    @37
    @32
    @4
    @3
    cK
    wf1
    #
    @39
    @0
    @40
    @27
    pwfseqlem4.k
    adantr
    #
    @4
    @3
    cK
    f1f
    syl
    @4
    @3
    cD
    cK
    ffvelrn
    sylancom
    @32
    @33
    cD
    @8
    @0
    @27
    @4
    cK
    crn
    #
    cK
    wf1o
    #
    @33
    cD
    wceq
    @32
    @40
    @43
    @41
    @4
    @3
    cK
    f1f1orn
    syl
    @4
    @42
    cD
    cK
    f1ocnvfv1
    sylancom
    #
    @0
    cD
    @8
    wcel
    @27
    @0
    cD
    @16
    @8
    pwfseqlem4.d
    @0
    cG
    @17
    wfn
    #
    @20
    @16
    @8
    wcel
    @0
    @18
    @45
    @19
    @17
    @2
    cG
    f1fn
    syl
    @26
    @17
    @15
    cG
    fnfvelrn
    syl2anc
    syl5eqel
    adantr
    eqeltrd
    @29
    @37
    @38
    wa
    #
    @36
    @29
    @37
    @38
    @36
    wa
    #
    wa
    @46
    @36
    wa
    vy
    cv
    #
    @6
    cfv
    #
    @8
    wcel
    #
    @48
    @49
    @10
    cfv
    #
    wcel
    #
    wn
    #
    wa
    #
    @47
    vy
    @28
    @3
    @15
    @48
    @28
    wceq
    #
    @50
    @38
    @53
    @36
    @55
    @49
    @33
    @8
    @48
    @28
    @6
    fveq2
    #
    eleq1d
    @55
    @52
    @35
    @55
    @48
    @28
    @51
    @34
    @55
    id
    @55
    @49
    @33
    @10
    @56
    fveq2d
    eleq12d
    notbid
    anbi12d
    @14
    @54
    vw
    vy
    @3
    @5
    @48
    wceq
    #
    @9
    @50
    @13
    @53
    @57
    @7
    @49
    @8
    @5
    @48
    @6
    fveq2
    #
    eleq1d
    @57
    @12
    @52
    @57
    @5
    @48
    @11
    @51
    @57
    id
    @57
    @7
    @49
    @10
    @58
    fveq2d
    eleq12d
    notbid
    anbi12d
    cbvrabv
    elrab2
    @37
    @38
    @36
    anass
    bitr4i
    baib
    syl2anc
    @32
    @35
    @29
    @32
    @34
    @15
    @28
    @32
    @34
    @16
    @10
    cfv
    #
    @15
    @32
    @33
    @16
    @10
    @32
    @33
    cD
    @16
    @44
    pwfseqlem4.d
    syl6eq
    fveq2d
    @0
    @59
    @15
    wceq
    #
    @27
    @0
    @17
    @8
    cG
    wf1o
    #
    @20
    @60
    @0
    @18
    @61
    @19
    @17
    @2
    cG
    f1f1orn
    syl
    @26
    @17
    @8
    @15
    cG
    f1ocnvfv1
    syl2anc
    adantr
    eqtrd
    eleq2d
    notbid
    bitrd
    ex
    mtoi
    eldifd
end
