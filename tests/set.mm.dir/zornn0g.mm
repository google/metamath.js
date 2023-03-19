include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "crpss.mm"
include "wor.mm"
include "w3a.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "wpss.mm"
include "wn.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "wrex.mm"
include "simp2.mm"
include "wa.mm"
include "simp1.mm"
include "cfn.mm"
include "snfi.mm"
include "finnum.mm"
include "ax-mp.mm"
include "unnum.mm"
include "sylancl.mm"
include "cdif.mm"
include "uncom.mm"
include "sseq2i.mm"
include "ssundif.mm"
include "bitri.mm"
include "difss.mm"
include "soss.mm"
include "wceq.mm"
include "wb.mm"
include "ssdif0.mm"
include "uni0b.mm"
include "biimpri.mm"
include "eleq1d.mm"
include "sylbir.mm"
include "imbi2d.mm"
include "cvv.mm"
include "vex.mm"
include "difexg.mm"
include "sseq1.mm"
include "neeq1.mm"
include "soeq2.mm"
include "3anbi123d.mm"
include "unieq.mm"
include "imbi12d.mm"
include "spcv.mm"
include "com12.mm"
include "3expa.mm"
include "an32s.mm"
include "unidif0.mm"
include "eleq1i.mm"
include "elun1.mm"
include "sylbi.mm"
include "syl6.mm"
include "0ex.mm"
include "snid.mm"
include "elun2.mm"
include "2a1i.mm"
include "pm2.61ne.mm"
include "sylan2.mm"
include "sylanb.mm"
include "alrimiv.mm"
include "3ad2ant3.mm"
include "zorng.mm"
include "syl2anc.mm"
include "ssun1.mm"
include "ssralv.mm"
include "reximi.mm"
include "wo.mm"
include "rexun.mm"
include "simpr.mm"
include "psseq1.mm"
include "0pss.mm"
include "syl6bb.mm"
include "notbid.mm"
include "nne.mm"
include "ralbidv.mm"
include "rexsn.mm"
include "eqsn.mm"
include "biimpar.mm"
include "sylan2b.mm"
include "rexeqdv.mm"
include "mpbird.mm"
include "jaodan.mm"

theorem zornn0g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint s x
  disjoint r x
  disjoint q x
  disjoint d x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint R x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint g y
  disjoint h y
  disjoint t y
  disjoint s y
  disjoint r y
  disjoint q y
  disjoint d y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint R y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint g z
  disjoint h z
  disjoint t z
  disjoint s z
  disjoint r z
  disjoint q z
  disjoint d z
  disjoint k z
  disjoint m z
  disjoint n z
  disjoint R z
  disjoint v w
  disjoint u w
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint s w
  disjoint r w
  disjoint q w
  disjoint d w
  disjoint k w
  disjoint m w
  disjoint n w
  disjoint R w
  disjoint u v
  disjoint g v
  disjoint h v
  disjoint t v
  disjoint s v
  disjoint r v
  disjoint q v
  disjoint d v
  disjoint k v
  disjoint m v
  disjoint n v
  disjoint R v
  disjoint g u
  disjoint h u
  disjoint t u
  disjoint s u
  disjoint r u
  disjoint q u
  disjoint d u
  disjoint k u
  disjoint m u
  disjoint n u
  disjoint R u
  disjoint g h
  disjoint g t
  disjoint g s
  disjoint g r
  disjoint g q
  disjoint d g
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint R g
  disjoint h t
  disjoint h s
  disjoint h r
  disjoint h q
  disjoint d h
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint R h
  disjoint s t
  disjoint r t
  disjoint q t
  disjoint d t
  disjoint k t
  disjoint m t
  disjoint n t
  disjoint R t
  disjoint r s
  disjoint q s
  disjoint d s
  disjoint k s
  disjoint m s
  disjoint n s
  disjoint R s
  disjoint q r
  disjoint d r
  disjoint k r
  disjoint m r
  disjoint n r
  disjoint R r
  disjoint d q
  disjoint k q
  disjoint m q
  disjoint n q
  disjoint R q
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint R d
  disjoint k m
  disjoint k n
  disjoint R k
  disjoint m n
  disjoint R m
  disjoint R n
  disjoint A w
  disjoint A v
  disjoint A u
  disjoint A g
  disjoint A h
  disjoint A t
  disjoint A s
  disjoint A r
  disjoint A q
  disjoint A d
  disjoint A k
  disjoint A m
  disjoint A n
  assert |- ( ( A e. dom card /\ A =/= (/) /\ A. z ( ( z C_ A /\ z =/= (/) /\ [C.] Or z ) -> U. z e. A ) ) -> E. x e. A A. y e. A -. x C. y )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    c0
    wne
    #
    vz
    cv
    #
    cA
    wss
    #
    @3
    c0
    wne
    #
    @3
    crpss
    wor
    #
    w3a
    #
    @3
    cuni
    #
    cA
    wcel
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    @2
    vx
    cv
    #
    vy
    cv
    #
    wpss
    #
    wn
    #
    vy
    cA
    c0
    csn
    #
    cun
    #
    wral
    #
    vx
    @18
    wrex
    #
    @16
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @1
    @2
    @11
    simp2
    @12
    @18
    @0
    wcel
    #
    vw
    cv
    #
    @18
    wss
    #
    @24
    crpss
    wor
    #
    wa
    #
    @24
    cuni
    #
    @18
    wcel
    #
    wi
    #
    vw
    wal
    #
    @20
    @12
    @1
    @17
    @0
    wcel
    #
    @23
    @1
    @2
    @11
    simp1
    @17
    cfn
    wcel
    @32
    c0
    snfi
    @17
    finnum
    ax-mp
    cA
    @17
    unnum
    sylancl
    @11
    @1
    @31
    @2
    @11
    @30
    vw
    @27
    @11
    @29
    @25
    @24
    @17
    cdif
    #
    cA
    wss
    #
    @26
    @11
    @29
    wi
    #
    @25
    @24
    @17
    cA
    cun
    #
    wss
    @34
    @18
    @36
    @24
    cA
    @17
    uncom
    sseq2i
    @24
    @17
    cA
    ssundif
    bitri
    @26
    @34
    @33
    crpss
    wor
    #
    @35
    @33
    @24
    wss
    @26
    @37
    wi
    @24
    @17
    difss
    @33
    @24
    crpss
    soss
    ax-mp
    @34
    @37
    wa
    #
    @35
    @11
    c0
    @18
    wcel
    #
    wi
    @33
    c0
    @33
    c0
    wceq
    #
    @29
    @39
    @11
    @40
    @24
    @17
    wss
    #
    @29
    @39
    wb
    @24
    @17
    ssdif0
    @41
    @28
    c0
    @18
    @28
    c0
    wceq
    @41
    @24
    uni0b
    biimpri
    eleq1d
    sylbir
    imbi2d
    @38
    @33
    c0
    wne
    #
    wa
    @11
    @33
    cuni
    #
    cA
    wcel
    #
    @29
    @34
    @42
    @37
    @11
    @44
    wi
    #
    @34
    @42
    @37
    @45
    @11
    @34
    @42
    @37
    w3a
    #
    @44
    @10
    @46
    @44
    wi
    vz
    @33
    @24
    cvv
    wcel
    @33
    cvv
    wcel
    vw
    vex
    @24
    @17
    cvv
    difexg
    ax-mp
    @3
    @33
    wceq
    #
    @7
    @46
    @9
    @44
    @47
    @4
    @34
    @5
    @42
    @6
    @37
    @3
    @33
    cA
    sseq1
    @3
    @33
    c0
    neeq1
    @3
    @33
    crpss
    soeq2
    3anbi123d
    @47
    @8
    @43
    cA
    @3
    @33
    unieq
    eleq1d
    imbi12d
    spcv
    com12
    3expa
    an32s
    @44
    @28
    cA
    wcel
    @29
    @43
    @28
    cA
    @24
    unidif0
    eleq1i
    @28
    cA
    @17
    elun1
    sylbi
    syl6
    @39
    @38
    @11
    c0
    @17
    wcel
    @39
    c0
    0ex
    snid
    c0
    @17
    cA
    elun2
    ax-mp
    2a1i
    pm2.61ne
    sylan2
    sylanb
    com12
    alrimiv
    3ad2ant3
    vx
    vy
    vw
    @18
    zorng
    syl2anc
    @20
    @2
    @21
    vx
    @18
    wrex
    #
    @22
    @19
    @21
    vx
    @18
    cA
    @18
    wss
    @19
    @21
    wi
    cA
    @17
    ssun1
    @16
    vy
    cA
    @18
    ssralv
    ax-mp
    reximi
    @48
    @2
    @22
    @21
    vx
    @17
    wrex
    #
    wo
    @22
    @21
    vx
    cA
    @17
    rexun
    @2
    @22
    @22
    @49
    @2
    @22
    simpr
    @2
    @49
    wa
    #
    @22
    @49
    @2
    @49
    simpr
    @50
    @21
    vx
    cA
    @17
    @49
    @2
    @14
    c0
    wceq
    #
    vy
    cA
    wral
    #
    cA
    @17
    wceq
    #
    @21
    @52
    vx
    c0
    0ex
    @13
    c0
    wceq
    #
    @16
    @51
    vy
    cA
    @54
    @16
    @14
    c0
    wne
    #
    wn
    @51
    @54
    @15
    @55
    @54
    @15
    c0
    @14
    wpss
    @55
    @13
    c0
    @14
    psseq1
    @14
    0pss
    syl6bb
    notbid
    @14
    c0
    nne
    syl6bb
    ralbidv
    rexsn
    @2
    @53
    @52
    vy
    cA
    c0
    eqsn
    biimpar
    sylan2b
    rexeqdv
    mpbird
    jaodan
    sylan2b
    sylan2
    syl2anc
end
