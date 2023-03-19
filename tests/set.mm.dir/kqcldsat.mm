include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccld.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wb.mm"
include "wfn.mm"
include "kqffn.mm"
include "elpreima.mm"
include "syl.mm"
include "adantr.mm"
include "cdif.mm"
include "wn.mm"
include "wi.mm"
include "c0.mm"
include "noel.mm"
include "cin.mm"
include "elin.mm"
include "incom.mm"
include "wss.mm"
include "wceq.mm"
include "cdm.mm"
include "cuni.mm"
include "eqid.mm"
include "cldss.mm"
include "adantl.mm"
include "fndm.mm"
include "toponuni.mm"
include "eqtrd.mm"
include "sseqtr4d.mm"
include "sseqtrd.mm"
include "dfss4.mm"
include "sylib.mm"
include "imaeq2d.mm"
include "ineq2d.mm"
include "simpll.mm"
include "difeq1d.mm"
include "cldopn.mm"
include "eqeltrd.mm"
include "kqdisj.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "mtbiri.mm"
include "imnan.mm"
include "sylibr.mm"
include "eldif.mm"
include "baibr.mm"
include "simpr.mm"
include "kqfvima.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "con1bid.mm"
include "sylibd.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "sseqin2.mm"
include "dminss.mm"
include "syl6eqssr.mm"
include "eqssd.mm"

theorem kqcldsat
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint J o
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ( J e. ( TopOn ` X ) /\ U e. ( Clsd ` J ) ) -> ( `' F " ( F " U ) ) = U )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cU
    cJ
    ccld
    cfv
    wcel
    #
    wa
    #
    cF
    ccnv
    cF
    cU
    cima
    #
    cima
    #
    cU
    @3
    vz
    @5
    cU
    @3
    vz
    cv
    #
    @5
    wcel
    #
    @6
    cX
    wcel
    #
    @6
    cF
    cfv
    #
    @4
    wcel
    #
    wa
    #
    @6
    cU
    wcel
    #
    @1
    @7
    @11
    wb
    #
    @2
    @1
    cF
    cX
    wfn
    #
    @13
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    #
    cX
    @6
    @4
    cF
    elpreima
    syl
    adantr
    @3
    @8
    @10
    @12
    @3
    @8
    wa
    #
    @10
    @9
    cF
    cX
    cU
    cdif
    #
    cima
    #
    wcel
    #
    wn
    #
    @12
    @16
    @10
    @19
    wa
    #
    wn
    @10
    @20
    wi
    @16
    @21
    @9
    c0
    wcel
    #
    @9
    noel
    @21
    @9
    @4
    @18
    cin
    #
    wcel
    @16
    @22
    @9
    @4
    @18
    elin
    @16
    @23
    c0
    @9
    @16
    @23
    @18
    @4
    cin
    #
    c0
    @4
    @18
    incom
    @16
    @18
    cF
    cX
    @17
    cdif
    #
    cima
    #
    cin
    #
    @24
    c0
    @16
    @26
    @4
    @18
    @16
    @25
    cU
    cF
    @16
    cU
    cX
    wss
    #
    @25
    cU
    wceq
    @3
    @28
    @8
    @3
    cU
    cF
    cdm
    #
    cX
    @3
    cU
    cJ
    cuni
    #
    @29
    @2
    cU
    @30
    wss
    @1
    cU
    cJ
    @30
    @30
    eqid
    #
    cldss
    adantl
    @1
    @29
    @30
    wceq
    @2
    @1
    @29
    cX
    @30
    @1
    @14
    @29
    cX
    wceq
    #
    @15
    cX
    cF
    fndm
    syl
    #
    cX
    cJ
    toponuni
    #
    eqtrd
    adantr
    sseqtr4d
    #
    @1
    @32
    @2
    @33
    adantr
    sseqtrd
    adantr
    cU
    cX
    dfss4
    sylib
    imaeq2d
    ineq2d
    @16
    @1
    @17
    cJ
    wcel
    #
    @27
    c0
    wceq
    @1
    @2
    @8
    simpll
    #
    @3
    @36
    @8
    @3
    @17
    @30
    cU
    cdif
    #
    cJ
    @3
    cX
    @30
    cU
    @1
    cX
    @30
    wceq
    @2
    @34
    adantr
    difeq1d
    @2
    @38
    cJ
    wcel
    @1
    cU
    cJ
    @30
    @31
    cldopn
    adantl
    eqeltrd
    adantr
    #
    vx
    vy
    cX
    @17
    cF
    cJ
    cX
    kqval.2
    kqdisj
    syl2anc
    eqtr3d
    syl5eq
    eleq2d
    syl5bbr
    mtbiri
    @10
    @19
    imnan
    sylibr
    @16
    @12
    @19
    @16
    @12
    wn
    #
    @6
    @17
    wcel
    #
    @19
    @8
    @40
    @41
    wb
    @3
    @41
    @8
    @40
    @6
    cX
    cU
    eldif
    baibr
    adantl
    @16
    @1
    @36
    @8
    @41
    @19
    wb
    @37
    @39
    @3
    @8
    simpr
    vx
    vy
    @6
    @17
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    bitrd
    con1bid
    sylibd
    expimpd
    sylbid
    ssrdv
    @3
    cU
    @29
    cU
    cin
    #
    @5
    @3
    cU
    @29
    wss
    @42
    cU
    wceq
    @35
    cU
    @29
    sseqin2
    sylib
    cU
    cF
    dminss
    syl6eqssr
    eqssd
end
