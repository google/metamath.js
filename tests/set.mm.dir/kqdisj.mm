include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "cdif.mm"
include "cin.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "cdm.mm"
include "imadmres.mm"
include "dmres.mm"
include "wfn.mm"
include "kqffn.mm"
include "adantr.mm"
include "fndm.mm"
include "syl.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "indif1.mm"
include "inss2.mm"
include "ssdif.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "imass2.mm"
include "mp1i.mm"
include "eqsstrd.mm"
include "sslin.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "eldifn.mm"
include "adantl.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "eldifi.mm"
include "kqfvima.mm"
include "syl3anc.mm"
include "mtbid.mm"
include "ralrimiva.mm"
include "difss.mm"
include "eleq1.mm"
include "notbid.mm"
include "ralima.mm"
include "sylancl.mm"
include "mpbird.mm"
include "disjr.mm"
include "sylibr.mm"
include "sseq0.mm"
include "syl2anc.mm"

theorem kqdisj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
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
  disjoint A x
  disjoint A y
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
  disjoint y z
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
  assert |- ( ( J e. ( TopOn ` X ) /\ U e. J ) -> ( ( F " U ) i^i ( F " ( A \ U ) ) ) = (/) )

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
    wcel
    #
    wa
    #
    cF
    cU
    cima
    #
    cF
    cA
    cU
    cdif
    #
    cima
    #
    cin
    #
    @4
    cF
    cX
    cU
    cdif
    #
    cima
    #
    cin
    #
    wss
    #
    @10
    c0
    wceq
    #
    @7
    c0
    wceq
    @3
    @6
    @9
    wss
    @11
    @3
    @6
    cF
    @5
    cX
    cin
    #
    cima
    #
    @9
    @3
    @6
    cF
    cF
    @5
    cres
    cdm
    #
    cima
    @14
    cF
    @5
    imadmres
    @3
    @15
    @13
    cF
    @3
    @15
    @5
    cF
    cdm
    #
    cin
    @13
    cF
    @5
    dmres
    @3
    @16
    cX
    @5
    @3
    cF
    cX
    wfn
    #
    @16
    cX
    wceq
    @1
    @17
    @2
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    adantr
    #
    cX
    cF
    fndm
    syl
    ineq2d
    syl5eq
    imaeq2d
    syl5eqr
    @13
    @8
    wss
    @14
    @9
    wss
    @3
    @13
    cA
    cX
    cin
    #
    cU
    cdif
    #
    @8
    cA
    cX
    cU
    indif1
    @19
    cX
    wss
    @20
    @8
    wss
    cA
    cX
    inss2
    @19
    cX
    cU
    ssdif
    ax-mp
    eqsstri
    @13
    @8
    cF
    imass2
    mp1i
    eqsstrd
    @6
    @9
    @4
    sslin
    syl
    @3
    vz
    cv
    #
    @4
    wcel
    #
    wn
    #
    vz
    @9
    wral
    #
    @12
    @3
    @24
    vw
    cv
    #
    cF
    cfv
    #
    @4
    wcel
    #
    wn
    #
    vw
    @8
    wral
    #
    @3
    @28
    vw
    @8
    @3
    @25
    @8
    wcel
    #
    wa
    #
    @25
    cU
    wcel
    #
    @27
    @30
    @32
    wn
    @3
    @25
    cX
    cU
    eldifn
    adantl
    @31
    @1
    @2
    @25
    cX
    wcel
    #
    @32
    @27
    wb
    @1
    @2
    @30
    simpll
    @1
    @2
    @30
    simplr
    @30
    @33
    @3
    @25
    cX
    cU
    eldifi
    adantl
    vx
    vy
    @25
    cU
    cF
    cJ
    cX
    kqval.2
    kqfvima
    syl3anc
    mtbid
    ralrimiva
    @3
    @17
    @8
    cX
    wss
    @24
    @29
    wb
    @18
    cX
    cU
    difss
    @23
    @28
    vz
    vw
    cX
    @8
    cF
    @21
    @26
    wceq
    @22
    @27
    @21
    @26
    @4
    eleq1
    notbid
    ralima
    sylancl
    mpbird
    vz
    @4
    @9
    disjr
    sylibr
    @7
    @10
    sseq0
    syl2anc
end
