include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "crng.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wral.mm"
include "wrex.mm"
include "simpl.mm"
include "lidl0.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "jca.mm"
include "lidlrng.mm"
include "syl.mm"
include "eqcoms.mm"
include "id.mm"
include "eqid.mm"
include "ring0cl.mm"
include "ringlz.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "ralsng.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "rexsng.mm"
include "simpr.mm"
include "lidlbas.mm"
include "eqtrd.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "ex.mm"
include "sylbid.mm"
include "mpd.mm"
include "isringrng.mm"
include "sylibr.mm"

theorem zlidlring
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )
  assume zlidlring.b: |- B = ( Base ` R )
  assume zlidlring.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ U = { .0. } ) -> I e. Ring )

  proof
    cR
    crg
    wcel
    #
    cU
    c.0
    csn
    #
    wceq
    #
    wa
    #
    cI
    crng
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @6
    @5
    @7
    co
    #
    @6
    wceq
    #
    wa
    #
    vy
    cI
    cbs
    cfv
    #
    wral
    #
    vx
    @13
    wrex
    #
    wa
    cI
    crg
    wcel
    @3
    @4
    @15
    @3
    @0
    cU
    cL
    wcel
    #
    wa
    @4
    @3
    @0
    @16
    @0
    @2
    simpl
    @3
    @16
    @1
    cL
    wcel
    #
    @0
    @17
    @2
    cR
    cL
    c.0
    lidlabl.l
    zlidlring.0
    lidl0
    adantr
    #
    @2
    @16
    @17
    wb
    @0
    cU
    @1
    cL
    eleq1
    adantl
    mpbird
    jca
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlrng
    syl
    @3
    @17
    @15
    @18
    @3
    @17
    @16
    @15
    @2
    @17
    @16
    wb
    #
    @0
    @19
    @1
    cU
    @1
    cU
    cL
    eleq1
    eqcoms
    adantl
    @3
    @16
    @15
    @3
    @16
    wa
    #
    @15
    @5
    @6
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @6
    @5
    @21
    co
    #
    @6
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    vx
    @1
    wrex
    #
    @3
    @28
    @16
    @0
    @28
    @2
    @0
    @28
    c.0
    @6
    @21
    co
    #
    @6
    wceq
    #
    @6
    c.0
    @21
    co
    #
    @6
    wceq
    #
    wa
    #
    vy
    @1
    wral
    #
    @0
    @34
    c.0
    c.0
    @21
    co
    #
    c.0
    wceq
    #
    @36
    wa
    #
    @0
    @0
    c.0
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @37
    @0
    @0
    @39
    @0
    id
    @38
    cR
    c.0
    @38
    eqid
    #
    zlidlring.0
    ring0cl
    jca
    @40
    @36
    @36
    @38
    cR
    @21
    c.0
    c.0
    @41
    @21
    eqid
    #
    zlidlring.0
    ringlz
    #
    @43
    jca
    syl
    @0
    c.0
    cvv
    wcel
    #
    @34
    @37
    wb
    @44
    @0
    c.0
    cR
    c0g
    cfv
    cvv
    zlidlring.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    #
    @33
    @37
    vy
    c.0
    cvv
    @6
    c.0
    wceq
    #
    @30
    @36
    @32
    @36
    @46
    @29
    @35
    @6
    c.0
    @6
    c.0
    c.0
    @21
    oveq2
    @46
    id
    #
    eqeq12d
    @46
    @31
    @35
    @6
    c.0
    @6
    c.0
    c.0
    @21
    oveq1
    @47
    eqeq12d
    anbi12d
    ralsng
    syl
    mpbird
    @0
    @44
    @28
    @34
    wb
    @45
    @27
    @34
    vx
    c.0
    cvv
    @5
    c.0
    wceq
    #
    @26
    @33
    vy
    @1
    @48
    @23
    @30
    @25
    @32
    @48
    @22
    @29
    @6
    @5
    c.0
    @6
    @21
    oveq1
    eqeq1d
    @48
    @24
    @31
    @6
    @5
    c.0
    @6
    @21
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rexsng
    syl
    mpbird
    adantr
    adantr
    @20
    @14
    @27
    vx
    @13
    @1
    @20
    @13
    cU
    @1
    @20
    @16
    @13
    cU
    wceq
    @3
    @16
    simpr
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlbas
    syl
    @3
    @2
    @16
    @0
    @2
    simpr
    adantr
    eqtrd
    #
    @20
    @12
    @26
    vy
    @13
    @1
    @49
    @20
    @9
    @23
    @11
    @25
    @20
    @8
    @22
    @6
    @20
    @7
    @21
    @5
    @6
    @16
    @7
    @21
    wceq
    @3
    @16
    @21
    @7
    cU
    cR
    cI
    @21
    cL
    lidlabl.i
    @42
    ressmulr
    eqcomd
    adantl
    #
    oveqd
    eqeq1d
    @20
    @10
    @24
    @6
    @20
    @7
    @21
    @6
    @5
    @50
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    rexeqbidv
    mpbird
    ex
    sylbid
    mpd
    jca
    vx
    vy
    @13
    cI
    @7
    @13
    eqid
    @7
    eqid
    isringrng
    sylibr
end
