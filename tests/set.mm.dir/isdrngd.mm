include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "wa.mm"
include "cdr.mm"
include "wss.mm"
include "wceq.mm"
include "difss.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "syl.mm"
include "cmulr.mm"
include "cplusg.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "difexg.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "3syl.mm"
include "eqtrd.mm"
include "cv.mm"
include "wne.mm"
include "eldifsn.mm"
include "w3a.mm"
include "ringcl.mm"
include "syl3an1.mm"
include "3expib.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "3imtr4d.mm"
include "3impib.mm"
include "3adant2r.mm"
include "3adant3r.mm"
include "sylanbrc.mm"
include "syl3an3b.mm"
include "syl3an2b.mm"
include "eldifi.mm"
include "3anim123i.mm"
include "wi.mm"
include "ringass.mm"
include "ex.mm"
include "3anbi123d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "imp.mm"
include "sylan2.mm"
include "cur.mm"
include "ringidcl.mm"
include "3eltr4d.mm"
include "ringlidm.mm"
include "eqeq1d.mm"
include "adantrr.mm"
include "sylan2b.mm"
include "isgrpd.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "mpbi2and.mm"
include "isdrng2.mm"
include "sylibr.mm"

theorem isdrngd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let c.0: class .0.
  let vz: setvar z
  assume isdrngd.b: |- ( ph -> B = ( Base ` R ) )
  assume isdrngd.t: |- ( ph -> .x. = ( .r ` R ) )
  assume isdrngd.z: |- ( ph -> .0. = ( 0g ` R ) )
  assume isdrngd.u: |- ( ph -> .1. = ( 1r ` R ) )
  assume isdrngd.r: |- ( ph -> R e. Ring )
  assume isdrngd.n: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) /\ ( y e. B /\ y =/= .0. ) ) -> ( x .x. y ) =/= .0. )
  assume isdrngd.o: |- ( ph -> .1. =/= .0. )
  assume isdrngd.i: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> I e. B )
  assume isdrngd.j: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> I =/= .0. )
  assume isdrngd.k: |- ( ( ph /\ ( x e. B /\ x =/= .0. ) ) -> ( I .x. x ) = .1. )

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint .1. x
  disjoint .1. y
  disjoint B x
  disjoint B y
  disjoint I y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint .x. x
  disjoint .x. y
  disjoint x z
  disjoint y z
  disjoint .0. z
  disjoint .1. z
  disjoint B z
  disjoint I z
  disjoint R z
  disjoint ph z
  disjoint .x. z
  assert |- ( ph -> R e. DivRing )

  proof
    wph
    cR
    crg
    wcel
    #
    cR
    cmgp
    cfv
    #
    cR
    cbs
    cfv
    #
    cR
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cress
    co
    #
    cgrp
    wcel
    #
    wa
    #
    cR
    cdr
    wcel
    wph
    @0
    @1
    cB
    c.0
    csn
    #
    cdif
    #
    cress
    co
    #
    cgrp
    wcel
    #
    @8
    isdrngd.r
    wph
    vx
    vy
    vz
    @10
    c.x
    @11
    cI
    c.1
    wph
    @10
    @2
    wss
    @10
    @11
    cbs
    cfv
    wceq
    wph
    cB
    @10
    @2
    cB
    @9
    difss
    isdrngd.b
    syl5sseq
    @10
    @2
    @11
    @1
    @11
    eqid
    #
    @2
    cR
    @1
    @1
    eqid
    #
    @2
    eqid
    #
    mgpbas
    ressbas2
    syl
    wph
    c.x
    cR
    cmulr
    cfv
    #
    @11
    cplusg
    cfv
    #
    isdrngd.t
    wph
    cB
    cvv
    wcel
    @10
    cvv
    wcel
    @16
    @17
    wceq
    wph
    cB
    @2
    cvv
    isdrngd.b
    cR
    cbs
    fvex
    syl6eqel
    cB
    @9
    cvv
    difexg
    @10
    @16
    @1
    @11
    cvv
    @13
    cR
    @16
    @1
    @14
    @16
    eqid
    #
    mgpplusg
    ressplusg
    3syl
    eqtrd
    vx
    cv
    #
    @10
    wcel
    #
    wph
    @19
    cB
    wcel
    #
    @19
    c.0
    wne
    #
    wa
    #
    vy
    cv
    #
    @10
    wcel
    #
    @19
    @24
    c.x
    co
    #
    @10
    wcel
    #
    @19
    cB
    c.0
    eldifsn
    #
    @25
    wph
    @23
    @24
    cB
    wcel
    #
    @24
    c.0
    wne
    #
    wa
    #
    @27
    @24
    cB
    c.0
    eldifsn
    wph
    @23
    @31
    w3a
    @26
    cB
    wcel
    #
    @26
    c.0
    wne
    @27
    wph
    @23
    @29
    @32
    @30
    wph
    @21
    @29
    @32
    @22
    wph
    @21
    @29
    @32
    wph
    @19
    @2
    wcel
    #
    @24
    @2
    wcel
    #
    wa
    @19
    @24
    @16
    co
    #
    @2
    wcel
    #
    @21
    @29
    wa
    @32
    wph
    @33
    @34
    @36
    wph
    @0
    @33
    @34
    @36
    isdrngd.r
    @2
    cR
    @16
    @19
    @24
    @15
    @18
    ringcl
    syl3an1
    3expib
    wph
    @21
    @33
    @29
    @34
    wph
    cB
    @2
    @19
    isdrngd.b
    eleq2d
    #
    wph
    cB
    @2
    @24
    isdrngd.b
    eleq2d
    #
    anbi12d
    wph
    @26
    @35
    cB
    @2
    wph
    c.x
    @16
    @19
    @24
    isdrngd.t
    oveqd
    #
    isdrngd.b
    eleq12d
    3imtr4d
    3impib
    3adant2r
    3adant3r
    isdrngd.n
    @26
    cB
    c.0
    eldifsn
    sylanbrc
    syl3an3b
    syl3an2b
    @20
    @25
    vz
    cv
    #
    @10
    wcel
    #
    w3a
    wph
    @21
    @29
    @40
    cB
    wcel
    #
    w3a
    #
    @26
    @40
    c.x
    co
    #
    @19
    @24
    @40
    c.x
    co
    #
    c.x
    co
    #
    wceq
    #
    @20
    @21
    @25
    @29
    @41
    @42
    @19
    cB
    @9
    eldifi
    @24
    cB
    @9
    eldifi
    @40
    cB
    @9
    eldifi
    3anim123i
    wph
    @43
    @47
    wph
    @33
    @34
    @40
    @2
    wcel
    #
    w3a
    #
    @35
    @40
    @16
    co
    #
    @19
    @24
    @40
    @16
    co
    #
    @16
    co
    #
    wceq
    #
    @43
    @47
    wph
    @0
    @49
    @53
    wi
    isdrngd.r
    @0
    @49
    @53
    @2
    cR
    @16
    @19
    @24
    @40
    @15
    @18
    ringass
    ex
    syl
    wph
    @21
    @33
    @29
    @34
    @42
    @48
    @37
    @38
    wph
    cB
    @2
    @40
    isdrngd.b
    eleq2d
    3anbi123d
    wph
    @44
    @50
    @46
    @52
    wph
    @26
    @35
    @40
    @40
    c.x
    @16
    isdrngd.t
    @39
    wph
    @40
    eqidd
    oveq123d
    wph
    @19
    @19
    @45
    @51
    c.x
    @16
    isdrngd.t
    wph
    @19
    eqidd
    #
    wph
    c.x
    @16
    @24
    @40
    isdrngd.t
    oveqd
    oveq123d
    eqeq12d
    3imtr4d
    imp
    sylan2
    wph
    c.1
    cB
    wcel
    c.1
    c.0
    wne
    c.1
    @10
    wcel
    wph
    cR
    cur
    cfv
    #
    @2
    c.1
    cB
    wph
    @0
    @55
    @2
    wcel
    isdrngd.r
    @2
    cR
    @55
    @15
    @55
    eqid
    #
    ringidcl
    syl
    isdrngd.u
    isdrngd.b
    3eltr4d
    isdrngd.o
    c.1
    cB
    c.0
    eldifsn
    sylanbrc
    @20
    wph
    @23
    c.1
    @19
    c.x
    co
    #
    @19
    wceq
    #
    @28
    wph
    @21
    @58
    @22
    wph
    @21
    @58
    wph
    @33
    @55
    @19
    @16
    co
    #
    @19
    wceq
    #
    @21
    @58
    wph
    @0
    @33
    @60
    wi
    isdrngd.r
    @0
    @33
    @60
    @2
    cR
    @16
    @55
    @19
    @15
    @18
    @56
    ringlidm
    ex
    syl
    @37
    wph
    @57
    @59
    @19
    wph
    c.1
    @55
    @19
    @19
    c.x
    @16
    isdrngd.t
    isdrngd.u
    @54
    oveq123d
    eqeq1d
    3imtr4d
    imp
    adantrr
    sylan2b
    @20
    wph
    @23
    cI
    @10
    wcel
    #
    @28
    wph
    @23
    wa
    cI
    cB
    wcel
    cI
    c.0
    wne
    @61
    isdrngd.i
    isdrngd.j
    cI
    cB
    c.0
    eldifsn
    sylanbrc
    sylan2b
    @20
    wph
    @23
    cI
    @19
    c.x
    co
    c.1
    wceq
    @28
    isdrngd.k
    sylan2b
    isgrpd
    wph
    @12
    @7
    @0
    wph
    @11
    @6
    cgrp
    wph
    @10
    @5
    @1
    cress
    wph
    cB
    @2
    @9
    @4
    isdrngd.b
    wph
    c.0
    @3
    isdrngd.z
    sneqd
    difeq12d
    oveq2d
    eleq1d
    anbi2d
    mpbi2and
    @2
    cR
    @6
    @3
    @15
    @3
    eqid
    @6
    eqid
    isdrng2
    sylibr
end
