include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "simpl3.mm"
include "cn0.mm"
include "simpl2.mm"
include "odcl.mm"
include "syl.mm"
include "nn0zd.mm"
include "bezout.mm"
include "syl2anc.mm"
include "wi.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "cplusg.mm"
include "simpll1.mm"
include "adantr.mm"
include "simprl.mm"
include "zmulcld.mm"
include "simprr.mm"
include "eqid.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "c0g.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "mulgass.mm"
include "eqtrd.mm"
include "cdvds.mm"
include "wbr.mm"
include "dvdsmul1.mm"
include "wb.mm"
include "oddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq12d.mm"
include "mulgcl.mm"
include "grprid.mm"
include "simplr.mm"
include "mulg1.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem odbezout
  let vx: setvar x
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let vy: setvar y
  assume odmulgid.1: |- X = ( Base ` G )
  assume odmulgid.2: |- O = ( od ` G )
  assume odmulgid.3: |- .x. = ( .g ` G )

  disjoint A x
  disjoint G x
  disjoint N x
  disjoint O x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint N y
  disjoint O y
  disjoint .x. y
  disjoint X y
  assert |- ( ( ( G e. Grp /\ A e. X /\ N e. ZZ ) /\ ( N gcd ( O ` A ) ) = 1 ) -> E. x e. ZZ ( x .x. ( N .x. A ) ) = A )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cN
    cA
    cO
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    @5
    cN
    vx
    cv
    #
    cmul
    co
    #
    @4
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    #
    vx
    cz
    wrex
    #
    @8
    cN
    cA
    c.x
    co
    #
    c.x
    co
    #
    cA
    wceq
    #
    vx
    cz
    wrex
    @7
    @2
    @4
    cz
    wcel
    #
    @15
    @0
    @1
    @2
    @6
    simpl3
    #
    @7
    @4
    @7
    @1
    @4
    cn0
    wcel
    #
    @0
    @1
    @2
    @6
    simpl2
    #
    cA
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    #
    syl
    nn0zd
    vx
    vy
    cN
    @4
    bezout
    syl2anc
    @7
    @14
    @18
    vx
    cz
    @7
    @8
    cz
    wcel
    #
    wa
    @13
    @18
    vy
    cz
    @7
    @24
    @10
    cz
    wcel
    #
    @13
    @18
    wi
    @13
    @12
    cA
    c.x
    co
    #
    @5
    cA
    c.x
    co
    #
    wceq
    #
    @7
    @24
    @25
    wa
    #
    wa
    #
    @18
    @28
    @12
    @5
    @12
    @5
    cA
    c.x
    oveq1
    eqcoms
    @30
    @26
    @17
    @27
    cA
    @30
    @26
    @9
    cA
    c.x
    co
    #
    @11
    cA
    c.x
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @17
    @30
    @0
    @9
    cz
    wcel
    @11
    cz
    wcel
    #
    @1
    @26
    @34
    wceq
    @0
    @1
    @2
    @6
    @29
    simpll1
    #
    @30
    cN
    @8
    @7
    @2
    @29
    @20
    adantr
    #
    @7
    @24
    @25
    simprl
    #
    zmulcld
    @30
    @4
    @10
    @30
    @4
    @30
    @1
    @21
    @7
    @1
    @29
    @22
    adantr
    #
    @23
    syl
    nn0zd
    #
    @7
    @24
    @25
    simprr
    #
    zmulcld
    #
    @39
    cX
    @33
    c.x
    cG
    @9
    @11
    cA
    odmulgid.1
    odmulgid.3
    @33
    eqid
    #
    mulgdir
    syl13anc
    @30
    @34
    @17
    cG
    c0g
    cfv
    #
    @33
    co
    #
    @17
    @30
    @31
    @17
    @32
    @44
    @33
    @30
    @31
    @8
    cN
    cmul
    co
    #
    cA
    c.x
    co
    #
    @17
    @30
    @9
    @46
    cA
    c.x
    @30
    cN
    @8
    @30
    cN
    @37
    zcnd
    @30
    @8
    @38
    zcnd
    mulcomd
    oveq1d
    @30
    @0
    @24
    @2
    @1
    @47
    @17
    wceq
    @36
    @38
    @37
    @39
    cX
    c.x
    cG
    @8
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgass
    syl13anc
    eqtrd
    @30
    @4
    @11
    cdvds
    wbr
    #
    @32
    @44
    wceq
    #
    @30
    @19
    @25
    @48
    @40
    @41
    @4
    @10
    dvdsmul1
    syl2anc
    @30
    @0
    @1
    @35
    @48
    @49
    wb
    @36
    @39
    @42
    cA
    c.x
    cG
    @11
    cO
    cX
    @44
    odmulgid.1
    odmulgid.2
    odmulgid.3
    @44
    eqid
    #
    oddvds
    syl3anc
    mpbid
    oveq12d
    @30
    @0
    @17
    cX
    wcel
    #
    @45
    @17
    wceq
    @36
    @30
    @0
    @24
    @16
    cX
    wcel
    #
    @51
    @36
    @38
    @30
    @0
    @2
    @1
    @52
    @36
    @37
    @39
    cX
    c.x
    cG
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgcl
    syl3anc
    cX
    c.x
    cG
    @8
    @16
    odmulgid.1
    odmulgid.3
    mulgcl
    syl3anc
    cX
    @33
    cG
    @17
    @44
    odmulgid.1
    @43
    @50
    grprid
    syl2anc
    eqtrd
    eqtrd
    @30
    @27
    c1
    cA
    c.x
    co
    #
    cA
    @30
    @5
    c1
    cA
    c.x
    @3
    @6
    @29
    simplr
    oveq1d
    @30
    @1
    @53
    cA
    wceq
    @39
    cX
    c.x
    cG
    cA
    odmulgid.1
    odmulgid.3
    mulg1
    syl
    eqtrd
    eqeq12d
    syl5ib
    anassrs
    rexlimdva
    reximdva
    mpd
end
