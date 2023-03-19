include "cplusg.mm"
include "cfv.mm"
include "cmulr.mm"
include "cbs.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "cstv.mm"
include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "co.mm"
include "3adant2.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqid.mm"
include "grpcl.mm"
include "syl3an1.mm"
include "3adant3.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "crngcom.mm"
include "ringcl.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "issrngd.mm"

theorem idsrngd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.as: class .*
  let va: setvar a
  let vb: setvar b
  assume idsrngd.k: |- B = ( Base ` R )
  assume idsrngd.c: |- .* = ( *r ` R )
  assume idsrngd.r: |- ( ph -> R e. CRing )
  assume idsrngd.i: |- ( ( ph /\ x e. B ) -> ( .* ` x ) = x )

  disjoint .* x
  disjoint B x
  disjoint R x
  disjoint ph x
  disjoint a b
  disjoint a x
  disjoint B a
  disjoint b x
  disjoint B b
  disjoint R a
  disjoint R b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> R e. *Ring )

  proof
    wph
    va
    vb
    cR
    cplusg
    cfv
    #
    cR
    cR
    cmulr
    cfv
    #
    c.as
    cB
    cB
    cR
    cbs
    cfv
    wceq
    wph
    idsrngd.k
    a1i
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    c.as
    cR
    cstv
    cfv
    wceq
    wph
    idsrngd.c
    a1i
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    #
    idsrngd.r
    cR
    crngring
    syl
    #
    wph
    va
    cv
    #
    cB
    wcel
    #
    wa
    #
    @5
    c.as
    cfv
    #
    @5
    cB
    @7
    vx
    cv
    #
    c.as
    cfv
    #
    @9
    wceq
    #
    vx
    cB
    wral
    #
    @8
    @5
    wceq
    #
    wph
    @12
    @6
    wph
    @11
    vx
    cB
    idsrngd.i
    ralrimiva
    #
    adantr
    @7
    @11
    @13
    vx
    @5
    cB
    wph
    @6
    simpr
    #
    @7
    @9
    @5
    wceq
    #
    wa
    #
    @10
    @8
    @9
    @5
    @17
    @9
    @5
    c.as
    @7
    @16
    simpr
    #
    fveq2d
    @18
    eqeq12d
    rspcdv
    mpd
    #
    @15
    eqeltrd
    wph
    @6
    vb
    cv
    #
    cB
    wcel
    #
    w3a
    #
    @5
    @20
    @0
    co
    #
    c.as
    cfv
    #
    @23
    @8
    @20
    c.as
    cfv
    #
    @0
    co
    @22
    @12
    @24
    @23
    wceq
    #
    wph
    @21
    @12
    @6
    wph
    @12
    @21
    @14
    adantr
    #
    3adant2
    #
    @22
    @11
    @26
    vx
    @23
    cB
    wph
    cR
    cgrp
    wcel
    #
    @6
    @21
    @23
    cB
    wcel
    wph
    @3
    @29
    @4
    cR
    ringgrp
    syl
    cB
    @0
    cR
    @5
    @20
    idsrngd.k
    @0
    eqid
    grpcl
    syl3an1
    @22
    @9
    @23
    wceq
    #
    wa
    #
    @10
    @24
    @9
    @23
    @31
    @9
    @23
    c.as
    @22
    @30
    simpr
    #
    fveq2d
    @32
    eqeq12d
    rspcdv
    mpd
    @22
    @8
    @5
    @25
    @20
    @0
    wph
    @6
    @13
    @21
    @19
    3adant3
    #
    wph
    @21
    @25
    @20
    wceq
    #
    @6
    wph
    @21
    wa
    #
    @12
    @34
    @27
    @35
    @11
    @34
    vx
    @20
    cB
    wph
    @21
    simpr
    @35
    @9
    @20
    wceq
    #
    wa
    #
    @10
    @25
    @9
    @20
    @37
    @9
    @20
    c.as
    @35
    @36
    simpr
    #
    fveq2d
    @38
    eqeq12d
    rspcdv
    mpd
    3adant2
    #
    oveq12d
    eqtr4d
    @22
    @5
    @20
    @1
    co
    #
    @20
    @5
    @1
    co
    #
    @40
    c.as
    cfv
    #
    @25
    @8
    @1
    co
    wph
    @2
    @6
    @21
    @40
    @41
    wceq
    idsrngd.r
    cB
    cR
    @1
    @5
    @20
    idsrngd.k
    @1
    eqid
    #
    crngcom
    syl3an1
    @22
    @12
    @42
    @40
    wceq
    #
    @28
    @22
    @11
    @44
    vx
    @40
    cB
    wph
    @3
    @6
    @21
    @40
    cB
    wcel
    @4
    cB
    cR
    @1
    @5
    @20
    idsrngd.k
    @43
    ringcl
    syl3an1
    @22
    @9
    @40
    wceq
    #
    wa
    #
    @10
    @42
    @9
    @40
    @46
    @9
    @40
    c.as
    @22
    @45
    simpr
    #
    fveq2d
    @47
    eqeq12d
    rspcdv
    mpd
    @22
    @25
    @20
    @8
    @5
    @1
    @39
    @33
    oveq12d
    3eqtr4d
    @7
    @8
    c.as
    cfv
    @8
    @5
    @7
    @8
    @5
    c.as
    @19
    fveq2d
    @19
    eqtrd
    issrngd
end
