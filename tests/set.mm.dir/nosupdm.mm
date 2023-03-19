include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cdm.mm"
include "wcel.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cab.mm"
include "cfv.mm"
include "w3a.mm"
include "cio.mm"
include "cmpt.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cif.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "iotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "weq.mm"
include "dmeq.mm"
include "eleq2d.mm"
include "breq1.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "breq2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "rexbidv.mm"
include "cbvabv.mm"

theorem nosupdm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let vg: setvar g
  let vq: setvar q
  let vp: setvar p
  assume nosupdm.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A p
  disjoint A q
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q y
  disjoint q z
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint y z
  assert |- ( -. E. x e. A A. y e. A -. x <s y -> dom S = { z | E. p e. A ( z e. dom p /\ A. q e. A ( -. q <s p -> ( p |` suc z ) = ( q |` suc z ) ) ) } )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    wn
    #
    cS
    cdm
    #
    @1
    vu
    cv
    #
    cdm
    #
    wcel
    #
    vv
    cv
    #
    @6
    cslt
    wbr
    #
    wn
    #
    @6
    @1
    csuc
    #
    cres
    #
    @9
    @12
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    vy
    cab
    #
    vz
    cv
    #
    vp
    cv
    #
    cdm
    #
    wcel
    #
    vq
    cv
    #
    @22
    cslt
    wbr
    #
    wn
    #
    @22
    @21
    csuc
    #
    cres
    #
    @25
    @28
    cres
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    vz
    cab
    @4
    @5
    vg
    @20
    vg
    cv
    #
    @7
    wcel
    @11
    @6
    @36
    csuc
    #
    cres
    @9
    @37
    cres
    wceq
    wi
    vv
    cA
    wral
    @36
    @6
    cfv
    @0
    wceq
    w3a
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cdm
    @20
    @4
    cS
    @40
    @4
    cS
    @3
    @2
    vx
    cA
    crio
    #
    @41
    cdm
    c2o
    cop
    csn
    cun
    #
    @40
    cif
    @40
    nosupdm.1
    @3
    @42
    @40
    iffalse
    syl5eq
    dmeqd
    vg
    @20
    @39
    @40
    @38
    vx
    iotaex
    @40
    eqid
    dmmpti
    syl6eq
    @19
    @35
    vy
    vz
    @19
    @1
    @23
    wcel
    #
    @27
    @22
    @12
    cres
    #
    @25
    @12
    cres
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    vy
    vz
    weq
    #
    @35
    @18
    @49
    vu
    vp
    cA
    vu
    vp
    weq
    #
    @8
    @43
    @17
    @48
    @51
    @7
    @23
    @1
    @6
    @22
    dmeq
    eleq2d
    @17
    @25
    @6
    cslt
    wbr
    #
    wn
    #
    @13
    @45
    wceq
    #
    wi
    #
    vq
    cA
    wral
    @51
    @48
    @16
    @55
    vv
    vq
    cA
    vv
    vq
    weq
    #
    @11
    @53
    @15
    @54
    @56
    @10
    @52
    @9
    @25
    @6
    cslt
    breq1
    notbid
    @56
    @14
    @45
    @13
    @9
    @25
    @12
    reseq1
    eqeq2d
    imbi12d
    cbvralv
    @51
    @55
    @47
    vq
    cA
    @51
    @53
    @27
    @54
    @46
    @51
    @52
    @26
    @6
    @22
    @25
    cslt
    breq2
    notbid
    @51
    @13
    @44
    @45
    @6
    @22
    @12
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    syl5bb
    anbi12d
    cbvrexv
    @50
    @49
    @34
    vp
    cA
    @50
    @43
    @24
    @48
    @33
    @1
    @21
    @23
    eleq1
    @50
    @47
    @32
    vq
    cA
    @50
    @46
    @31
    @27
    @50
    @44
    @29
    @45
    @30
    @50
    @12
    @28
    @22
    @1
    @21
    suceq
    #
    reseq2d
    @50
    @12
    @28
    @25
    @57
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    syl5bb
    cbvabv
    syl6eq
end
