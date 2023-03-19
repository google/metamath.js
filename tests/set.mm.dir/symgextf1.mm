include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "symgextf.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wb.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "wo.mm"
include "elun.mm"
include "symgextfv.mm"
include "com12.mm"
include "imp.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "wf1o.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf1o.mm"
include "f1of1.mm"
include "dff13.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "equequ2.mm"
include "rspc2va.mm"
include "expcom.mm"
include "a1d.mm"
include "sylbi.mm"
include "3syl.mm"
include "impcom.mm"
include "sylbid.mm"
include "ex.mm"
include "wne.mm"
include "symgextf1lem.mm"
include "eqneqall.mm"
include "eqcoms.mm"
include "syl6com.mm"
include "ancoms.mm"
include "elsni.mm"
include "eqtr3.mm"
include "2a1d.mm"
include "syl2an.mm"
include "ccase.mm"
include "syl2anb.mm"
include "ralrimivv.mm"
include "sylanbrc.mm"

theorem symgextf1
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cZ: class Z
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  disjoint Y x
  disjoint E y
  disjoint E z
  disjoint y z
  disjoint K i
  disjoint K j
  disjoint K y
  disjoint i j
  disjoint i y
  disjoint j y
  disjoint K z
  disjoint N i
  disjoint N j
  disjoint N y
  disjoint N z
  disjoint S y
  disjoint S z
  disjoint Z i
  disjoint Z j
  disjoint Z y
  disjoint Z z
  disjoint x y
  disjoint x z
  disjoint j z
  assert |- ( ( K e. N /\ Z e. S ) -> E : N -1-1-> N )

  proof
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    wa
    #
    cN
    cN
    cE
    wf
    vy
    cv
    #
    cE
    cfv
    #
    vz
    cv
    #
    cE
    cfv
    #
    wceq
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    cN
    wral
    vy
    cN
    wral
    cN
    cN
    cE
    wf1
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextf
    @2
    @9
    vy
    vz
    cN
    cN
    @2
    @3
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    wa
    #
    @3
    cN
    cK
    csn
    #
    cdif
    #
    @13
    cun
    #
    wcel
    #
    @5
    @15
    wcel
    #
    wa
    #
    @9
    @0
    @12
    @18
    wb
    @1
    @0
    @10
    @16
    @11
    @17
    @0
    cN
    @15
    @3
    @0
    @15
    cN
    cN
    cK
    difsnid
    eqcomd
    #
    eleq2d
    @0
    cN
    @15
    @5
    @19
    eleq2d
    anbi12d
    adantr
    @18
    @2
    @9
    @16
    @3
    @14
    wcel
    #
    @3
    @13
    wcel
    #
    wo
    @5
    @14
    wcel
    #
    @5
    @13
    wcel
    #
    wo
    @2
    @9
    wi
    #
    @17
    @3
    @14
    @13
    elun
    @5
    @14
    @13
    elun
    @20
    @22
    @21
    @23
    @24
    @20
    @22
    wa
    #
    @2
    @9
    @25
    @2
    wa
    #
    @7
    @3
    cZ
    cfv
    #
    @5
    cZ
    cfv
    #
    wceq
    #
    @8
    @26
    @4
    @27
    @6
    @28
    @25
    @2
    @4
    @27
    wceq
    #
    @20
    @2
    @30
    wi
    @22
    @2
    @20
    @30
    vx
    cS
    cE
    cK
    cN
    @3
    cZ
    symgext.s
    symgext.e
    symgextfv
    com12
    adantr
    imp
    @25
    @2
    @6
    @28
    wceq
    #
    @22
    @2
    @31
    wi
    @20
    @2
    @22
    @31
    vx
    cS
    cE
    cK
    cN
    @5
    cZ
    symgext.s
    symgext.e
    symgextfv
    com12
    adantl
    imp
    eqeq12d
    @2
    @25
    @29
    @8
    wi
    #
    @1
    @0
    @25
    @32
    wi
    #
    @1
    @14
    @14
    cZ
    wf1o
    @14
    @14
    cZ
    wf1
    #
    @0
    @33
    wi
    #
    @14
    cS
    cZ
    @14
    csymg
    cfv
    #
    @36
    eqid
    symgext.s
    symgbasf1o
    @14
    @14
    cZ
    f1of1
    @34
    @14
    @14
    cZ
    wf
    #
    vi
    cv
    #
    cZ
    cfv
    #
    vj
    cv
    #
    cZ
    cfv
    #
    wceq
    #
    vi
    vj
    weq
    #
    wi
    #
    vj
    @14
    wral
    vi
    @14
    wral
    #
    wa
    @35
    vi
    vj
    @14
    @14
    cZ
    dff13
    @45
    @35
    @37
    @45
    @33
    @0
    @25
    @45
    @32
    @44
    @32
    @27
    @41
    wceq
    #
    vy
    vj
    weq
    #
    wi
    vi
    vj
    @3
    @5
    @14
    @14
    vi
    vy
    weq
    #
    @42
    @46
    @43
    @47
    @48
    @39
    @27
    @41
    @38
    @3
    cZ
    fveq2
    eqeq1d
    vi
    vy
    vj
    equequ1
    imbi12d
    vj
    vz
    weq
    #
    @46
    @29
    @47
    @8
    @49
    @41
    @28
    @27
    @40
    @5
    cZ
    fveq2
    eqeq2d
    vj
    vz
    vy
    equequ2
    imbi12d
    rspc2va
    expcom
    a1d
    adantl
    sylbi
    3syl
    impcom
    impcom
    sylbid
    ex
    @22
    @21
    @24
    @2
    @22
    @21
    wa
    @6
    @4
    wne
    #
    @9
    vx
    cS
    cE
    cK
    cN
    @5
    @3
    cZ
    symgext.s
    symgext.e
    symgextf1lem
    @7
    @50
    @8
    @50
    @8
    wi
    @6
    @4
    @8
    @6
    @4
    eqneqall
    eqcoms
    com12
    syl6com
    ancoms
    @2
    @20
    @23
    wa
    @4
    @6
    wne
    #
    @9
    vx
    cS
    cE
    cK
    cN
    @3
    @5
    cZ
    symgext.s
    symgext.e
    symgextf1lem
    @7
    @51
    @8
    @8
    @4
    @6
    eqneqall
    com12
    syl6com
    @21
    @3
    cK
    wceq
    #
    @5
    cK
    wceq
    #
    @24
    @23
    @3
    cK
    elsni
    @5
    cK
    elsni
    @52
    @53
    wa
    @8
    @2
    @7
    @3
    @5
    cK
    eqtr3
    2a1d
    syl2an
    ccase
    syl2anb
    com12
    sylbid
    ralrimivv
    vy
    vz
    cN
    cN
    cE
    dff13
    sylanbrc
end
