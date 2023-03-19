include "cgrp.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "pwsgrp.mm"
include "syl2anc.mm"
include "cvv.mm"
include "simp3.mm"
include "ssexd.mm"
include "pwssplit0.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cres.mm"
include "cof.mm"
include "wceq.mm"
include "offres.mm"
include "adantl.mm"
include "adantr.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprr.mm"
include "pwsplusgval.mm"
include "reseq1d.mm"
include "fvtresfn.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "isghmd.mm"

theorem pwssplit2
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let cT: class T
  assume pwssplit1.y: |- Y = ( W ^s U )
  assume pwssplit1.z: |- Z = ( W ^s V )
  assume pwssplit1.b: |- B = ( Base ` Y )
  assume pwssplit1.c: |- C = ( Base ` Z )
  assume pwssplit1.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint Y x
  disjoint W x
  disjoint U x
  disjoint Z x
  disjoint V x
  disjoint B x
  disjoint C x
  disjoint X x
  disjoint Y a
  disjoint Y b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint W a
  disjoint W b
  disjoint U a
  disjoint U b
  disjoint Z a
  disjoint Z b
  disjoint V a
  disjoint V b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint X a
  disjoint X b
  disjoint T x
  assert |- ( ( W e. Grp /\ U e. X /\ V C_ U ) -> F e. ( Y GrpHom Z ) )

  proof
    cW
    cgrp
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
    va
    vb
    cY
    cplusg
    cfv
    #
    cZ
    cplusg
    cfv
    #
    cY
    cZ
    cF
    cB
    cC
    pwssplit1.b
    pwssplit1.c
    @4
    eqid
    #
    @5
    eqid
    #
    @3
    @0
    @1
    cY
    cgrp
    wcel
    #
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
    cW
    cU
    cX
    cY
    pwssplit1.y
    pwsgrp
    syl2anc
    #
    @3
    @0
    cV
    cvv
    wcel
    #
    cZ
    cgrp
    wcel
    @9
    @3
    cV
    cU
    cX
    @10
    @0
    @1
    @2
    simp3
    ssexd
    #
    cW
    cV
    cvv
    cZ
    pwssplit1.z
    pwsgrp
    syl2anc
    vx
    cB
    cC
    cgrp
    cU
    cF
    cV
    cW
    cX
    cY
    cZ
    pwssplit1.y
    pwssplit1.z
    pwssplit1.b
    pwssplit1.c
    pwssplit1.f
    pwssplit0
    #
    @3
    va
    cv
    #
    cB
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    @15
    @17
    @4
    co
    #
    cV
    cres
    #
    @15
    cF
    cfv
    #
    @17
    cF
    cfv
    #
    cW
    cplusg
    cfv
    #
    cof
    #
    co
    #
    @21
    cF
    cfv
    #
    @23
    @24
    @5
    co
    @20
    @15
    @17
    @26
    co
    #
    cV
    cres
    #
    @15
    cV
    cres
    #
    @17
    cV
    cres
    #
    @26
    co
    #
    @22
    @27
    @19
    @30
    @33
    wceq
    @3
    cV
    @25
    @15
    @17
    cB
    cB
    offres
    adantl
    @20
    @21
    @29
    cV
    @20
    cB
    @25
    @4
    cW
    @15
    @17
    cU
    cgrp
    cX
    cY
    pwssplit1.y
    pwssplit1.b
    @3
    @0
    @19
    @9
    adantr
    #
    @0
    @1
    @2
    @19
    simpl2
    @3
    @16
    @18
    simprl
    @3
    @16
    @18
    simprr
    @25
    eqid
    #
    @6
    pwsplusgval
    reseq1d
    @19
    @27
    @33
    wceq
    @3
    @16
    @18
    @23
    @31
    @24
    @32
    @26
    vx
    cB
    cF
    cV
    @15
    pwssplit1.f
    fvtresfn
    vx
    cB
    cF
    cV
    @17
    pwssplit1.f
    fvtresfn
    oveqan12d
    adantl
    3eqtr4d
    @20
    @21
    cB
    wcel
    #
    @28
    @22
    wceq
    @3
    @8
    @19
    @36
    @11
    @8
    @16
    @18
    @36
    cB
    @4
    cY
    @15
    @17
    pwssplit1.b
    @6
    grpcl
    3expb
    sylan
    vx
    cB
    cF
    cV
    @21
    pwssplit1.f
    fvtresfn
    syl
    @20
    cC
    @25
    @5
    cW
    @23
    @24
    cV
    cgrp
    cvv
    cZ
    pwssplit1.z
    pwssplit1.c
    @34
    @3
    @12
    @19
    @13
    adantr
    @3
    @16
    @23
    cC
    wcel
    @18
    @3
    cB
    cC
    @15
    cF
    @14
    ffvelrnda
    adantrr
    @3
    @18
    @24
    cC
    wcel
    @16
    @3
    cB
    cC
    @17
    cF
    @14
    ffvelrnda
    adantrl
    @35
    @7
    pwsplusgval
    3eqtr4d
    isghmd
end
