include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "co.mm"
include "cress.mm"
include "clmhm.mm"
include "cbs.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "clss.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "frlmlss.mm"
include "syl2anc.mm"
include "lssss.mm"
include "resmpt.mm"
include "3syl.mm"
include "syl6eqr.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "pwssplit3.mm"
include "syl3an1.mm"
include "reslmhm.mm"
include "crn.mm"
include "wb.mm"
include "cvv.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ssexd.mm"
include "pwslmod.mm"
include "rneqd.mm"
include "wf.mm"
include "wa.mm"
include "cmap.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "frlmbasf.mm"
include "sylan.mm"
include "simpl3.mm"
include "fssresd.mm"
include "fvex.mm"
include "elmapg.mm"
include "sylancr.mm"
include "adantr.mm"
include "mpbird.mm"
include "frlmbasfsupp.mm"
include "fvexd.mm"
include "fsuppres.mm"
include "frlmelbas.mm"
include "mpbir2and.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"
include "reslmhm2b.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "frlmpws.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"

theorem frlmsplit2
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frlmsplit2.y: |- Y = ( R freeLMod U )
  assume frlmsplit2.z: |- Z = ( R freeLMod V )
  assume frlmsplit2.b: |- B = ( Base ` Y )
  assume frlmsplit2.c: |- C = ( Base ` Z )
  assume frlmsplit2.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint Y x
  disjoint R x
  disjoint U x
  disjoint Z x
  disjoint V x
  disjoint B x
  disjoint C x
  disjoint X x
  assert |- ( ( R e. Ring /\ U e. X /\ V C_ U ) -> F e. ( Y LMHom Z ) )

  proof
    cR
    crg
    wcel
    #
    cU
    cX
    wcel
    #
    cV
    cU
    wss
    #
    w3a
    #
    cF
    cR
    crglmod
    cfv
    #
    cU
    cpws
    co
    #
    cB
    cress
    co
    #
    @4
    cV
    cpws
    co
    #
    cC
    cress
    co
    #
    clmhm
    co
    #
    cY
    cZ
    clmhm
    co
    @3
    vx
    @5
    cbs
    cfv
    #
    vx
    cv
    #
    cV
    cres
    #
    cmpt
    #
    cB
    cres
    #
    cF
    @9
    @3
    @14
    vx
    cB
    @12
    cmpt
    #
    cF
    @3
    cB
    @5
    clss
    cfv
    #
    wcel
    #
    cB
    @10
    wss
    @14
    @15
    wceq
    @3
    @0
    @1
    @17
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    cB
    cR
    @16
    cY
    cU
    cX
    frlmsplit2.y
    frlmsplit2.b
    @16
    eqid
    #
    frlmlss
    syl2anc
    #
    @16
    cB
    @10
    @5
    @10
    eqid
    #
    @20
    lssss
    vx
    @10
    cB
    @12
    resmpt
    3syl
    #
    frlmsplit2.f
    syl6eqr
    @3
    @14
    @6
    @7
    clmhm
    co
    wcel
    #
    @14
    @9
    wcel
    #
    @3
    @13
    @5
    @7
    clmhm
    co
    wcel
    #
    @17
    @24
    @0
    @4
    clmod
    wcel
    #
    @1
    @2
    @26
    cR
    rlmlmod
    #
    vx
    @10
    @7
    cbs
    cfv
    #
    cU
    @13
    cV
    @4
    cX
    @5
    @7
    @5
    eqid
    @7
    eqid
    #
    @22
    @29
    eqid
    @13
    eqid
    pwssplit3
    syl3an1
    @21
    @6
    @5
    @7
    @16
    @13
    cB
    @20
    @6
    eqid
    reslmhm
    syl2anc
    @3
    @7
    clmod
    wcel
    #
    cC
    @7
    clss
    cfv
    #
    wcel
    #
    @14
    crn
    #
    cC
    wss
    @24
    @25
    wb
    @3
    @27
    cV
    cvv
    wcel
    #
    @31
    @0
    @1
    @27
    @2
    @28
    3ad2ant1
    @3
    cV
    cU
    cX
    @19
    @0
    @1
    @2
    simp3
    ssexd
    #
    @4
    cV
    cvv
    @7
    @30
    pwslmod
    syl2anc
    @3
    @0
    @35
    @33
    @18
    @36
    cC
    cR
    @32
    cZ
    cV
    cvv
    frlmsplit2.z
    frlmsplit2.c
    @32
    eqid
    #
    frlmlss
    syl2anc
    @3
    @34
    @15
    crn
    #
    cC
    @3
    @14
    @15
    @23
    rneqd
    @3
    cB
    cC
    @15
    wf
    @38
    cC
    wss
    @3
    vx
    cB
    @12
    cC
    @15
    @3
    @11
    cB
    wcel
    #
    wa
    #
    @12
    cC
    wcel
    #
    @12
    cR
    cbs
    cfv
    #
    cV
    cmap
    co
    wcel
    #
    @12
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @40
    @43
    cV
    @42
    @12
    wf
    #
    @40
    cU
    @42
    cV
    @11
    @3
    @1
    @39
    cU
    @42
    @11
    wf
    @19
    cB
    cR
    cY
    cU
    @42
    cX
    @11
    frlmsplit2.y
    @42
    eqid
    #
    frlmsplit2.b
    frlmbasf
    sylan
    @0
    @1
    @2
    @39
    simpl3
    fssresd
    @3
    @43
    @46
    wb
    #
    @39
    @3
    @42
    cvv
    wcel
    @35
    @48
    cR
    cbs
    fvex
    @36
    @42
    cV
    @12
    cvv
    cvv
    elmapg
    sylancr
    adantr
    mpbird
    @40
    @11
    cvv
    cV
    @44
    @3
    @1
    @39
    @11
    @44
    cfsupp
    wbr
    @19
    cB
    cR
    cY
    cU
    cX
    @11
    @44
    frlmsplit2.y
    @44
    eqid
    #
    frlmsplit2.b
    frlmbasfsupp
    sylan
    @40
    cR
    c0g
    fvexd
    fsuppres
    @3
    @41
    @43
    @45
    wa
    wb
    #
    @39
    @3
    @0
    @35
    @50
    @18
    @36
    cC
    cR
    cZ
    cV
    @42
    crg
    cvv
    @12
    @44
    frlmsplit2.z
    @47
    @49
    frlmsplit2.c
    frlmelbas
    syl2anc
    adantr
    mpbir2and
    @15
    eqid
    fmptd
    cB
    cC
    @15
    frn
    syl
    eqsstrd
    @6
    @7
    @8
    @14
    @32
    cC
    @8
    eqid
    @37
    reslmhm2b
    syl3anc
    mpbid
    eqeltrrd
    @3
    cY
    @6
    cZ
    @8
    clmhm
    @3
    @0
    @1
    cY
    @6
    wceq
    @18
    @19
    cB
    cR
    cY
    cU
    crg
    cX
    frlmsplit2.y
    frlmsplit2.b
    frlmpws
    syl2anc
    @3
    @0
    @35
    cZ
    @8
    wceq
    @18
    @36
    cC
    cR
    cZ
    cV
    crg
    cvv
    frlmsplit2.z
    frlmsplit2.c
    frlmpws
    syl2anc
    oveq12d
    eleqtrrd
end
