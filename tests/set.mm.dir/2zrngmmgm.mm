include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "cz.mm"
include "c2.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "zmulcl.mm"
include "ad2ant2r.mm"
include "wi.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "nfim.mm"
include "simpll.mm"
include "simpl.mm"
include "syl2an.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "oveq1.mm"
include "ad3antlr.mm"
include "2cnd.mm"
include "cc.mm"
include "zcn.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "exp41.mm"
include "rexlimi.mm"
include "impcom.mm"
include "imp.mm"
include "cbvrexv.mm"
include "anbi2i.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "cc0.mm"
include "0even.mm"
include "2zrngbas.mm"
include "mgpbas.mm"
include "2zrngmul.mm"
include "mgpplusg.mm"
include "ismgmn0.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem 2zrngmmgm
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )
  assume 2zrngmmgm.1: |- M = ( mulGrp ` R )

  disjoint x z
  disjoint R x
  disjoint R z
  disjoint E x
  disjoint E z
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint E y
  disjoint M a
  disjoint M b
  disjoint k x
  assert |- M e. Mgm

  proof
    cM
    cmgm
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cmul
    co
    #
    cE
    wcel
    #
    vb
    cE
    wral
    va
    cE
    wral
    #
    @4
    va
    vb
    cE
    @1
    cE
    wcel
    @1
    cz
    wcel
    #
    @1
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @2
    cz
    wcel
    #
    @2
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @4
    @2
    cE
    wcel
    vz
    cv
    #
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    @10
    vz
    @1
    cz
    cE
    @16
    @1
    wceq
    @17
    @9
    vx
    cz
    @16
    @1
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @18
    @14
    vz
    @2
    cz
    cE
    @16
    @2
    wceq
    @17
    @13
    vx
    cz
    @16
    @2
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @11
    @15
    wa
    @3
    cz
    wcel
    #
    @3
    c2
    vy
    cv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cz
    wrex
    #
    @4
    @6
    @12
    @19
    @10
    @14
    @1
    @2
    zmulcl
    ad2ant2r
    @11
    @15
    @23
    @10
    @6
    @15
    @23
    wi
    #
    @9
    @6
    @24
    wi
    vx
    cz
    @6
    @24
    vx
    @6
    vx
    nfv
    @15
    @23
    vx
    @12
    @14
    vx
    @12
    vx
    nfv
    @13
    vx
    cz
    nfre1
    nfan
    @23
    vx
    nfv
    nfim
    nfim
    @7
    cz
    wcel
    #
    @9
    @6
    @15
    @23
    @25
    @9
    wa
    @6
    wa
    #
    @15
    wa
    #
    @22
    @3
    c2
    @7
    @2
    cmul
    co
    #
    cmul
    co
    #
    wceq
    #
    vy
    @28
    cz
    @26
    @25
    @12
    @28
    cz
    wcel
    @15
    @25
    @9
    @6
    simpll
    @12
    @14
    simpl
    @7
    @2
    zmulcl
    syl2an
    @20
    @28
    wceq
    #
    @22
    @30
    wb
    @27
    @31
    @21
    @29
    @3
    @20
    @28
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @27
    @3
    @8
    @2
    cmul
    co
    #
    @29
    @9
    @3
    @32
    wceq
    @25
    @6
    @15
    @1
    @8
    @2
    cmul
    oveq1
    ad3antlr
    @27
    c2
    @7
    @2
    @27
    2cnd
    @25
    @7
    cc
    wcel
    @9
    @6
    @15
    @7
    zcn
    ad3antrrr
    @15
    @2
    cc
    wcel
    #
    @26
    @12
    @33
    @14
    @2
    zcn
    adantr
    adantl
    mulassd
    eqtrd
    rspcedvd
    exp41
    rexlimi
    impcom
    imp
    @4
    @19
    @3
    @8
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    @19
    @23
    wa
    @18
    @35
    vz
    @3
    cz
    cE
    @16
    @3
    wceq
    @17
    @34
    vx
    cz
    @16
    @3
    @8
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @35
    @23
    @19
    @34
    @22
    vx
    vy
    cz
    @7
    @20
    wceq
    @8
    @21
    @3
    @7
    @20
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    anbi2i
    bitri
    sylanbrc
    syl2anb
    rgen2a
    cc0
    cE
    wcel
    @0
    @5
    wb
    vx
    vz
    cE
    2zrng.e
    0even
    va
    vb
    cc0
    cE
    cM
    cmul
    cE
    cR
    cM
    2zrngmmgm.1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    mgpbas
    cR
    cmul
    cM
    2zrngmmgm.1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngmul
    mgpplusg
    ismgmn0
    ax-mp
    mpbir
end
