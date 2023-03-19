include "cv.mm"
include "cminusg.mm"
include "cfv.mm"
include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cplusg.mm"
include "co.mm"
include "cbs.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "eqid.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "oveqd.mm"
include "3eltr4d.mm"
include "wa.mm"
include "adantr.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "grpass.mm"
include "syl13anc.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "grpidcl.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "grpinvcl.mm"
include "grplinv.mm"
include "imasgrp2.mm"

theorem imasgrp
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cN: class N
  let vy: setvar y
  let vz: setvar z
  assume imasgrp.u: |- ( ph -> U = ( F "s R ) )
  assume imasgrp.v: |- ( ph -> V = ( Base ` R ) )
  assume imasgrp.p: |- ( ph -> .+ = ( +g ` R ) )
  assume imasgrp.f: |- ( ph -> F : V -onto-> B )
  assume imasgrp.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .+ b ) ) = ( F ` ( p .+ q ) ) ) )
  assume imasgrp.r: |- ( ph -> R e. Grp )
  assume imasgrp.z: |- .0. = ( 0g ` R )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint R p
  disjoint R q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint .+ p
  disjoint .+ q
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .0. p
  disjoint .0. q
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint B v
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint N p
  disjoint N v
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint q y
  disjoint q z
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .+ x
  disjoint .+ y
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint .0. u
  disjoint .0. v
  disjoint .0. w
  disjoint .0. x
  assert |- ( ph -> ( U e. Grp /\ ( F ` .0. ) = ( 0g ` U ) ) )

  proof
    wph
    vx
    vy
    vz
    cB
    c.pl
    cR
    cU
    cF
    vx
    cv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    cV
    cgrp
    c.0
    vq
    vp
    va
    vb
    imasgrp.u
    imasgrp.v
    imasgrp.p
    imasgrp.f
    imasgrp.e
    imasgrp.r
    wph
    @0
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @0
    @4
    cR
    cplusg
    cfv
    #
    co
    #
    cR
    cbs
    cfv
    #
    @0
    @4
    c.pl
    co
    #
    cV
    @6
    cR
    cgrp
    wcel
    #
    @0
    @9
    wcel
    #
    @4
    @9
    wcel
    #
    @8
    @9
    wcel
    wph
    @3
    @11
    @5
    imasgrp.r
    3ad2ant1
    @6
    @0
    cV
    @9
    wph
    @3
    @5
    simp2
    wph
    @3
    cV
    @9
    wceq
    #
    @5
    imasgrp.v
    3ad2ant1
    #
    eleqtrd
    #
    @6
    @4
    cV
    @9
    wph
    @3
    @5
    simp3
    @15
    eleqtrd
    #
    @9
    @7
    cR
    @0
    @4
    @9
    eqid
    #
    @7
    eqid
    #
    grpcl
    syl3anc
    @6
    c.pl
    @7
    @0
    @4
    wph
    @3
    c.pl
    @7
    wceq
    #
    @5
    imasgrp.p
    3ad2ant1
    oveqd
    #
    @15
    3eltr4d
    wph
    @3
    @5
    vz
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @10
    @22
    c.pl
    co
    #
    @0
    @4
    @22
    c.pl
    co
    #
    c.pl
    co
    #
    cF
    @25
    @8
    @22
    @7
    co
    #
    @0
    @4
    @22
    @7
    co
    #
    @7
    co
    #
    @26
    @28
    @25
    @11
    @12
    @13
    @22
    @9
    wcel
    @29
    @31
    wceq
    wph
    @11
    @24
    imasgrp.r
    adantr
    wph
    @3
    @5
    @12
    @23
    @16
    3adant3r3
    wph
    @3
    @5
    @13
    @23
    @17
    3adant3r3
    @25
    @22
    cV
    @9
    wph
    @3
    @5
    @23
    simpr3
    wph
    @14
    @24
    imasgrp.v
    adantr
    eleqtrd
    @9
    @7
    cR
    @0
    @4
    @22
    @18
    @19
    grpass
    syl13anc
    @25
    @10
    @8
    @22
    @22
    c.pl
    @7
    wph
    @20
    @24
    imasgrp.p
    adantr
    #
    wph
    @3
    @5
    @10
    @8
    wceq
    @23
    @21
    3adant3r3
    @25
    @22
    eqidd
    oveq123d
    @25
    @0
    @0
    @27
    @30
    c.pl
    @7
    @32
    @25
    @0
    eqidd
    @25
    c.pl
    @7
    @4
    @22
    @32
    oveqd
    oveq123d
    3eqtr4d
    fveq2d
    wph
    c.0
    @9
    cV
    wph
    @11
    c.0
    @9
    wcel
    imasgrp.r
    @9
    cR
    c.0
    @18
    imasgrp.z
    grpidcl
    syl
    imasgrp.v
    eleqtrrd
    wph
    @3
    wa
    #
    c.0
    @0
    c.pl
    co
    #
    @0
    cF
    @33
    @34
    c.0
    @0
    @7
    co
    #
    @0
    @33
    c.pl
    @7
    c.0
    @0
    wph
    @20
    @3
    imasgrp.p
    adantr
    #
    oveqd
    @33
    @11
    @12
    @35
    @0
    wceq
    wph
    @11
    @3
    imasgrp.r
    adantr
    #
    wph
    @3
    @12
    wph
    cV
    @9
    @0
    imasgrp.v
    eleq2d
    biimpa
    #
    @9
    @7
    cR
    @0
    c.0
    @18
    @19
    imasgrp.z
    grplid
    syl2anc
    eqtrd
    fveq2d
    @33
    @2
    @9
    cV
    @33
    @11
    @12
    @2
    @9
    wcel
    @37
    @38
    @9
    cR
    @1
    @0
    @18
    @1
    eqid
    #
    grpinvcl
    syl2anc
    wph
    @14
    @3
    imasgrp.v
    adantr
    eleqtrrd
    @33
    @2
    @0
    c.pl
    co
    #
    c.0
    cF
    @33
    @40
    @2
    @0
    @7
    co
    #
    c.0
    @33
    c.pl
    @7
    @2
    @0
    @36
    oveqd
    @33
    @11
    @12
    @41
    c.0
    wceq
    @37
    @38
    @9
    @7
    cR
    @1
    @0
    c.0
    @18
    @19
    imasgrp.z
    @39
    grplinv
    syl2anc
    eqtrd
    fveq2d
    imasgrp2
end
