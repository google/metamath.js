include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "ccrd.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "ccda.mm"
include "cen.mm"
include "wbr.mm"
include "wral.mm"
include "inss2.mm"
include "sseli.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "snfi.mm"
include "wss.mm"
include "inss1.mm"
include "elpwid.mm"
include "con0.mm"
include "onfin2.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "sselda.mm"
include "pwfi.mm"
include "sylib.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "ficardid.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "cdaen.mm"
include "djudisj.mm"
include "3ad2ant3.mm"
include "cdaun.mm"
include "syl3anc.mm"
include "iunxun.mm"
include "syl6breqr.mm"
include "entr.mm"
include "carden2b.mm"
include "ficardom.mm"
include "nnacda.mm"
include "eqtr3d.mm"
include "ackbij1lem6.mm"
include "3adant3.mm"
include "ackbij1lem7.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"

theorem ackbij1lem9
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( A e. ( ~P _om i^i Fin ) /\ B e. ( ~P _om i^i Fin ) /\ ( A i^i B ) = (/) ) -> ( F ` ( A u. B ) ) = ( ( F ` A ) +o ( F ` B ) ) )

  proof
    cA
    com
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    #
    vy
    cA
    cB
    cun
    #
    vy
    cv
    #
    csn
    #
    @7
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    #
    vy
    cA
    @10
    ciun
    #
    ccrd
    cfv
    #
    vy
    cB
    @10
    ciun
    #
    ccrd
    cfv
    #
    coa
    co
    #
    @6
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    coa
    co
    #
    @5
    @14
    @16
    ccda
    co
    #
    ccrd
    cfv
    #
    @12
    @17
    @5
    @22
    @11
    cen
    wbr
    #
    @23
    @12
    wceq
    @5
    @22
    @13
    @15
    ccda
    co
    #
    cen
    wbr
    #
    @25
    @11
    cen
    wbr
    @24
    @5
    @14
    @13
    cen
    wbr
    #
    @16
    @15
    cen
    wbr
    #
    @26
    @5
    @13
    cfn
    wcel
    #
    @27
    @5
    cA
    cfn
    wcel
    #
    @10
    cfn
    wcel
    #
    vy
    cA
    wral
    @29
    @2
    @3
    @30
    @4
    @1
    cfn
    cA
    @0
    cfn
    inss2
    #
    sseli
    3ad2ant1
    @5
    @31
    vy
    cA
    @5
    @7
    cA
    wcel
    wa
    #
    @8
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    @31
    @7
    snfi
    #
    @33
    @7
    cfn
    wcel
    #
    @35
    @5
    cA
    cfn
    @7
    @5
    cA
    com
    cfn
    @2
    @3
    cA
    com
    wss
    @4
    @2
    cA
    com
    @1
    @0
    cA
    @0
    cfn
    inss1
    #
    sseli
    elpwid
    3ad2ant1
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    #
    syl6ss
    sselda
    @7
    pwfi
    #
    sylib
    @8
    @9
    xpfi
    #
    sylancr
    ralrimiva
    vy
    cA
    @10
    iunfi
    syl2anc
    #
    @13
    ficardid
    syl
    @5
    @15
    cfn
    wcel
    #
    @28
    @5
    cB
    cfn
    wcel
    #
    @31
    vy
    cB
    wral
    @43
    @3
    @2
    @44
    @4
    @1
    cfn
    cB
    @32
    sseli
    3ad2ant2
    @5
    @31
    vy
    cB
    @5
    @7
    cB
    wcel
    wa
    #
    @34
    @35
    @31
    @36
    @45
    @37
    @35
    @5
    cB
    cfn
    @7
    @5
    cB
    com
    cfn
    @3
    @2
    cB
    com
    wss
    @4
    @3
    cB
    com
    @1
    @0
    cB
    @38
    sseli
    elpwid
    3ad2ant2
    @39
    syl6ss
    sselda
    @40
    sylib
    @41
    sylancr
    ralrimiva
    vy
    cB
    @10
    iunfi
    syl2anc
    #
    @15
    ficardid
    syl
    @14
    @13
    @16
    @15
    cdaen
    syl2anc
    @5
    @25
    @13
    @15
    cun
    #
    @11
    cen
    @5
    @29
    @43
    @13
    @15
    cin
    c0
    wceq
    #
    @25
    @47
    cen
    wbr
    @42
    @46
    @4
    @2
    @48
    @3
    vy
    vy
    cA
    cB
    @9
    @9
    djudisj
    3ad2ant3
    @13
    @15
    cfn
    cfn
    cdaun
    syl3anc
    vy
    cA
    cB
    @10
    iunxun
    syl6breqr
    @22
    @25
    @11
    entr
    syl2anc
    @22
    @11
    carden2b
    syl
    @5
    @14
    com
    wcel
    #
    @16
    com
    wcel
    #
    @23
    @17
    wceq
    @5
    @29
    @49
    @42
    @13
    ficardom
    syl
    @5
    @43
    @50
    @46
    @15
    ficardom
    syl
    @14
    @16
    nnacda
    syl2anc
    eqtr3d
    @5
    @6
    @1
    wcel
    #
    @18
    @12
    wceq
    @2
    @3
    @51
    @4
    cA
    cB
    ackbij1lem6
    3adant3
    vx
    vy
    @6
    cF
    ackbij.f
    ackbij1lem7
    syl
    @2
    @3
    @21
    @17
    wceq
    @4
    @2
    @3
    @19
    @14
    @20
    @16
    coa
    vx
    vy
    cA
    cF
    ackbij.f
    ackbij1lem7
    vx
    vy
    cB
    cF
    ackbij.f
    ackbij1lem7
    oveqan12d
    3adant3
    3eqtr4d
end
