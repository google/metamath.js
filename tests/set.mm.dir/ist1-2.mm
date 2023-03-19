include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct1.mm"
include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cuni.mm"
include "wral.mm"
include "wi.mm"
include "wceq.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "eqid.mm"
include "ist1.mm"
include "baib.mm"
include "syl.mm"
include "toponuni.mm"
include "raleqdv.mm"
include "wa.mm"
include "cdif.mm"
include "wss.mm"
include "wrex.mm"
include "adantr.mm"
include "eltop2.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "snssd.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "wne.mm"
include "imbi1d.mm"
include "wn.mm"
include "con1b.mm"
include "df-ne.mm"
include "imbi1i.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "elssuni.mm"
include "reldisj.mm"
include "syl5bbr.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "rexanali.mm"
include "bitr3i.mm"
include "con2bii.mm"
include "3bitr4ri.mm"
include "imbi2i.mm"
include "eldifsn.mm"
include "impexp.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "ralbidv2.mm"
include "3bitr4d.mm"
include "ralbidva.mm"
include "ralcom.mm"
include "syl6bb.mm"
include "3bitr2d.mm"

theorem ist1-2
  let vx: setvar x
  let vy: setvar y
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let cU: class U
  let cV: class V
  let cY: class Y

  disjoint x y
  disjoint o x
  disjoint o y
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint J f
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g o
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint J g
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
  disjoint m o
  disjoint J m
  disjoint n o
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Fre <-> A. x e. X A. y e. X ( A. o e. J ( x e. o -> y e. o ) -> x = y ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    ct1
    wcel
    #
    vy
    cv
    #
    csn
    #
    cJ
    ccld
    cfv
    wcel
    #
    vy
    cJ
    cuni
    #
    wral
    #
    @4
    vy
    cX
    wral
    #
    vx
    cv
    #
    vo
    cv
    #
    wcel
    #
    @2
    @9
    wcel
    #
    wi
    vo
    cJ
    wral
    #
    @8
    @2
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @0
    cJ
    ctop
    wcel
    #
    @1
    @6
    wb
    cX
    cJ
    topontop
    #
    @1
    @16
    @6
    cJ
    @5
    vy
    @5
    eqid
    #
    ist1
    baib
    syl
    @0
    @4
    vy
    cX
    @5
    cX
    cJ
    toponuni
    #
    raleqdv
    @0
    @7
    @14
    vx
    cX
    wral
    #
    vy
    cX
    wral
    @15
    @0
    @4
    @20
    vy
    cX
    @0
    @2
    cX
    wcel
    #
    wa
    #
    @5
    @3
    cdif
    #
    cJ
    wcel
    #
    @10
    @9
    @23
    wss
    #
    wa
    #
    vo
    cJ
    wrex
    #
    vx
    @23
    wral
    #
    @4
    @20
    @22
    @16
    @24
    @28
    wb
    @0
    @16
    @21
    @17
    adantr
    #
    vx
    vo
    @23
    cJ
    eltop2
    syl
    @22
    @16
    @3
    @5
    wss
    @4
    @24
    wb
    @29
    @22
    @2
    @5
    @0
    @21
    @2
    @5
    wcel
    @0
    cX
    @5
    @2
    @19
    eleq2d
    biimpa
    snssd
    @3
    cJ
    @5
    @18
    iscld2
    syl2anc
    @22
    @14
    @27
    vx
    cX
    @23
    @22
    @8
    cX
    wcel
    #
    @8
    @2
    wne
    #
    @27
    wi
    #
    wi
    @8
    @5
    wcel
    #
    @32
    wi
    #
    @30
    @14
    wi
    @8
    @23
    wcel
    #
    @27
    wi
    #
    @22
    @30
    @33
    @32
    @22
    cX
    @5
    @8
    @0
    cX
    @5
    wceq
    @21
    @19
    adantr
    eleq2d
    imbi1d
    @14
    @32
    @30
    @13
    wn
    #
    @27
    wi
    @27
    wn
    #
    @13
    wi
    @32
    @14
    @13
    @27
    con1b
    @31
    @37
    @27
    @8
    @2
    df-ne
    imbi1i
    @12
    @38
    @13
    @27
    @12
    @27
    @10
    @11
    wn
    #
    wa
    #
    vo
    cJ
    wrex
    @12
    wn
    @40
    @26
    vo
    cJ
    @9
    cJ
    wcel
    #
    @39
    @25
    @10
    @39
    @9
    @3
    cin
    c0
    wceq
    #
    @41
    @25
    @9
    @2
    disjsn
    @41
    @9
    @5
    wss
    @42
    @25
    wb
    @9
    cJ
    elssuni
    @9
    @3
    @5
    reldisj
    syl
    syl5bbr
    anbi2d
    rexbiia
    @10
    @11
    vo
    cJ
    rexanali
    bitr3i
    con2bii
    imbi1i
    3bitr4ri
    imbi2i
    @36
    @33
    @31
    wa
    #
    @27
    wi
    @34
    @35
    @43
    @27
    @8
    @5
    @2
    eldifsn
    imbi1i
    @33
    @31
    @27
    impexp
    bitri
    3bitr4g
    ralbidv2
    3bitr4d
    ralbidva
    @14
    vy
    vx
    cX
    cX
    ralcom
    syl6bb
    3bitr2d
end
