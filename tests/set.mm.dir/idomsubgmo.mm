include "cidom.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "csubg.mm"
include "wral.mm"
include "wrmo.mm"
include "w3a.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "cod.mm"
include "cdvds.mm"
include "cbs.mm"
include "crab.mm"
include "cvv.mm"
include "wss.mm"
include "fvex.mm"
include "rabex.mm"
include "simp2l.mm"
include "eqid.mm"
include "subgss.mm"
include "syl.mm"
include "wel.mm"
include "cfn.mm"
include "simpl2l.mm"
include "cn0.mm"
include "simp3l.mm"
include "simp1r.mm"
include "nnnn0d.mm"
include "eqeltrd.mm"
include "wb.mm"
include "vex.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "adantr.mm"
include "simpr.mm"
include "odsubdvds.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "ssrabdv.mm"
include "simp2r.mm"
include "simpl2r.mm"
include "simp3r.mm"
include "unssd.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "cle.mm"
include "idomodle.mm"
include "3ad2ant1.mm"
include "breqtrrd.mm"
include "a1i.mm"
include "hashbnd.mm"
include "hashdom.mm"
include "sylancl.mm"
include "mpbid.mm"
include "domtr.mm"
include "syl2anc.mm"
include "unex.mm"
include "ssun1.mm"
include "mp2.mm"
include "sbth.mm"
include "eqtr4d.mm"
include "hashen.mm"
include "fiuneneq.mm"
include "3expia.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rmo4.mm"

theorem idomsubgmo
  let vy: setvar y
  let cR: class R
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vz: setvar z
  assume idomsubgmo.g: |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) )

  disjoint G y
  disjoint N y
  disjoint R y
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G z
  disjoint N x
  disjoint N z
  disjoint R x
  disjoint R z
  assert |- ( ( R e. IDomn /\ N e. NN ) -> E* y e. ( SubGrp ` G ) ( # ` y ) = N )

  proof
    cR
    cidom
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    vy
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    vx
    cv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    vy
    vx
    weq
    #
    wi
    #
    vx
    cG
    csubg
    cfv
    #
    wral
    vy
    @12
    wral
    @5
    vy
    @12
    wrmo
    @2
    @11
    vy
    vx
    @12
    @12
    @2
    @3
    @12
    wcel
    #
    @6
    @12
    wcel
    #
    wa
    #
    @9
    @10
    @2
    @15
    @9
    w3a
    #
    @3
    @6
    cun
    #
    @3
    cen
    wbr
    #
    @10
    @16
    @17
    @3
    cdom
    wbr
    #
    @3
    @17
    cdom
    wbr
    #
    @18
    @16
    @17
    vz
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    cN
    cdvds
    wbr
    #
    vz
    cG
    cbs
    cfv
    #
    crab
    #
    cdom
    wbr
    #
    @26
    @3
    cdom
    wbr
    #
    @19
    @26
    cvv
    wcel
    #
    @16
    @17
    @26
    wss
    @27
    @24
    vz
    @25
    cG
    cbs
    fvex
    rabex
    #
    @16
    @3
    @6
    @26
    @16
    @24
    vz
    @25
    @3
    @16
    @13
    @3
    @25
    wss
    @2
    @13
    @14
    @9
    simp2l
    @25
    @3
    cG
    @25
    eqid
    #
    subgss
    syl
    @16
    vz
    vy
    wel
    #
    wa
    #
    @23
    @4
    cN
    cdvds
    @33
    @13
    @3
    cfn
    wcel
    #
    @32
    @23
    @4
    cdvds
    wbr
    @13
    @14
    @2
    @9
    @32
    simpl2l
    @16
    @34
    @32
    @16
    @4
    cn0
    wcel
    #
    @34
    @16
    @4
    cN
    cn0
    @2
    @15
    @5
    @8
    simp3l
    #
    @16
    cN
    @0
    @1
    @15
    @9
    simp1r
    nnnn0d
    #
    eqeltrd
    #
    @3
    cvv
    wcel
    #
    @34
    @35
    wb
    vy
    vex
    #
    @3
    cvv
    hashclb
    ax-mp
    sylibr
    #
    adantr
    @16
    @32
    simpr
    @21
    @3
    cG
    @22
    @22
    eqid
    #
    odsubdvds
    syl3anc
    @16
    @5
    @32
    @36
    adantr
    breqtrd
    ssrabdv
    @16
    @24
    vz
    @25
    @6
    @16
    @14
    @6
    @25
    wss
    @2
    @13
    @14
    @9
    simp2r
    @25
    @6
    cG
    @31
    subgss
    syl
    @16
    vz
    vx
    wel
    #
    wa
    #
    @23
    @7
    cN
    cdvds
    @44
    @14
    @6
    cfn
    wcel
    #
    @43
    @23
    @7
    cdvds
    wbr
    @13
    @14
    @2
    @9
    @43
    simpl2r
    @16
    @45
    @43
    @16
    @7
    cn0
    wcel
    #
    @45
    @16
    @7
    cN
    cn0
    @2
    @15
    @5
    @8
    simp3r
    #
    @37
    eqeltrd
    @6
    cvv
    wcel
    @45
    @46
    wb
    vx
    vex
    #
    @6
    cvv
    hashclb
    ax-mp
    sylibr
    #
    adantr
    @16
    @43
    simpr
    @21
    @6
    cG
    @22
    @42
    odsubdvds
    syl3anc
    @16
    @8
    @43
    @47
    adantr
    breqtrd
    ssrabdv
    unssd
    @17
    @26
    cvv
    ssdomg
    mpsyl
    @16
    @26
    chash
    cfv
    #
    @4
    cle
    wbr
    #
    @28
    @16
    @50
    cN
    @4
    cle
    @2
    @15
    @50
    cN
    cle
    wbr
    @9
    vz
    @25
    cR
    cG
    cN
    @22
    idomsubgmo.g
    @31
    @42
    idomodle
    3ad2ant1
    @36
    breqtrrd
    #
    @16
    @26
    cfn
    wcel
    #
    @39
    @51
    @28
    wb
    @16
    @29
    @35
    @51
    @53
    @29
    @16
    @30
    a1i
    @38
    @52
    @26
    @4
    cvv
    hashbnd
    syl3anc
    @40
    @26
    @3
    cvv
    hashdom
    sylancl
    mpbid
    @17
    @26
    @3
    domtr
    syl2anc
    @17
    cvv
    wcel
    @3
    @17
    wss
    @20
    @3
    @6
    @40
    @48
    unex
    @3
    @6
    ssun1
    @3
    @17
    cvv
    ssdomg
    mp2
    @17
    @3
    sbth
    sylancl
    @16
    @3
    @6
    cen
    wbr
    #
    @34
    @18
    @10
    wb
    @16
    @4
    @7
    wceq
    #
    @54
    @16
    @4
    cN
    @7
    @36
    @47
    eqtr4d
    @16
    @34
    @45
    @55
    @54
    wb
    @41
    @49
    @3
    @6
    hashen
    syl2anc
    mpbid
    @41
    @3
    @6
    fiuneneq
    syl2anc
    mpbid
    3expia
    ralrimivva
    @5
    @8
    vy
    vx
    @12
    @10
    @4
    @7
    cN
    @3
    @6
    chash
    fveq2
    eqeq1d
    rmo4
    sylibr
end
