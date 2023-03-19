include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "cminusg.mm"
include "cmulr.mm"
include "co.mm"
include "wa.mm"
include "weq.mm"
include "cplusg.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "lcdlvec.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "mapdpglem30a.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simpld.mm"
include "mapdpglem30b.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "crg.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "mapdpglem29.mm"
include "lcdvsass.mm"
include "oveq2d.mm"
include "lcdvscl.mm"
include "lcdvsub.mm"
include "mapdpglem28.mm"
include "lcd1.mm"
include "oveq1d.mm"
include "lcdlmod.mm"
include "lmodvs1.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"
include "3eqtr2rd.mm"
include "lvecindp2.mm"
include "rngnegr.mm"
include "eqeq12d.mm"
include "grpinv11.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "mpbid.mm"

theorem mapdpglem30
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume mapdpg.h: |- H = ( LHyp ` K )
  assume mapdpg.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdpg.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdpg.v: |- V = ( Base ` U )
  assume mapdpg.s: |- .- = ( -g ` U )
  assume mapdpg.z: |- .0. = ( 0g ` U )
  assume mapdpg.n: |- N = ( LSpan ` U )
  assume mapdpg.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdpg.f: |- F = ( Base ` C )
  assume mapdpg.r: |- R = ( -g ` C )
  assume mapdpg.j: |- J = ( LSpan ` C )
  assume mapdpg.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdpg.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdpg.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdpg.g: |- ( ph -> G e. F )
  assume mapdpg.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume mapdpg.e: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { G } ) )
  assume mapdpgem25.h1: |- ( ph -> ( h e. F /\ ( ( M ` ( N ` { Y } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R h ) } ) ) ) )
  assume mapdpgem25.i1: |- ( ph -> ( i e. F /\ ( ( M ` ( N ` { Y } ) ) = ( J ` { i } ) /\ ( M ` ( N ` { ( X .- Y ) } ) ) = ( J ` { ( G R i ) } ) ) ) )
  assume mapdpglem26.a: |- A = ( Scalar ` U )
  assume mapdpglem26.b: |- B = ( Base ` A )
  assume mapdpglem26.t: |- .x. = ( .s ` C )
  assume mapdpglem26.o: |- O = ( 0g ` A )
  assume mapdpglem28.ve: |- ( ph -> v e. B )
  assume mapdpglem28.u1: |- ( ph -> h = ( u .x. i ) )
  assume mapdpglem28.u2: |- ( ph -> ( G R h ) = ( v .x. ( G R i ) ) )
  assume mapdpglem28.ue: |- ( ph -> u e. B )

  disjoint h i
  disjoint h u
  disjoint h v
  disjoint i u
  disjoint i v
  disjoint u v
  disjoint B u
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint O u
  disjoint O v
  disjoint .x. u
  disjoint .x. v
  disjoint G v
  disjoint R v
  assert |- ( ph -> ( v = ( 1r ` A ) /\ v = u ) )

  proof
    wph
    vv
    cv
    #
    cA
    cur
    cfv
    #
    wceq
    #
    @0
    @1
    cA
    cminusg
    cfv
    #
    cfv
    #
    cA
    cmulr
    cfv
    #
    co
    #
    vu
    cv
    #
    @4
    @5
    co
    #
    wceq
    #
    wa
    @2
    vv
    vu
    weq
    #
    wa
    wph
    @0
    @6
    @1
    @8
    cC
    cplusg
    cfv
    #
    c.x
    cC
    csca
    cfv
    #
    @12
    cbs
    cfv
    #
    cJ
    cF
    cC
    cG
    vi
    cv
    #
    cC
    c0g
    cfv
    #
    mapdpg.f
    @11
    eqid
    #
    @12
    eqid
    #
    @13
    eqid
    #
    mapdpglem26.t
    @15
    eqid
    mapdpg.j
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlvec
    wph
    cG
    cF
    wcel
    #
    cG
    @15
    wne
    cG
    cF
    @15
    csn
    cdif
    #
    wcel
    mapdpg.g
    wph
    cC
    cR
    cU
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    mapdpg.k
    mapdpg.x
    mapdpg.y
    mapdpg.g
    mapdpg.ne
    mapdpg.e
    mapdpglem30a
    cG
    cF
    @15
    eldifsn
    sylanbrc
    wph
    @14
    cF
    wcel
    #
    @14
    @15
    wne
    @14
    @20
    wcel
    wph
    @21
    cY
    csn
    cN
    cfv
    cM
    cfv
    @14
    csn
    cJ
    cfv
    wceq
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cG
    @14
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    mapdpgem25.i1
    simpld
    #
    wph
    cC
    cR
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    mapdpg.k
    mapdpg.x
    mapdpg.y
    mapdpg.g
    mapdpg.ne
    mapdpg.e
    mapdpgem25.h1
    mapdpgem25.i1
    mapdpglem30b
    @14
    cF
    @15
    eldifsn
    sylanbrc
    wph
    @0
    cB
    @13
    mapdpglem28.ve
    wph
    cC
    @13
    @12
    cU
    cA
    cH
    cK
    cB
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    @17
    @18
    mapdpg.k
    lcdsbase
    #
    eleqtrrd
    wph
    @6
    cB
    @13
    wph
    cA
    crg
    wcel
    #
    @0
    cB
    wcel
    @4
    cB
    wcel
    #
    @6
    cB
    wcel
    wph
    cU
    clmod
    wcel
    @24
    wph
    cU
    cH
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpg.k
    dvhlmod
    cA
    cU
    mapdpglem26.a
    lmodring
    syl
    #
    mapdpglem28.ve
    wph
    cA
    cgrp
    wcel
    #
    @1
    cB
    wcel
    #
    @25
    wph
    @24
    @27
    @26
    cA
    ringgrp
    syl
    #
    wph
    @24
    @28
    @26
    cB
    cA
    @1
    mapdpglem26.b
    @1
    eqid
    #
    ringidcl
    syl
    #
    cB
    cA
    @3
    @1
    mapdpglem26.b
    @3
    eqid
    #
    grpinvcl
    syl2anc
    #
    cB
    cA
    @5
    @0
    @4
    mapdpglem26.b
    @5
    eqid
    #
    ringcl
    syl3anc
    @23
    eleqtrrd
    wph
    @1
    cB
    @13
    @31
    @23
    eleqtrrd
    wph
    @8
    cB
    @13
    wph
    @24
    @7
    cB
    wcel
    @25
    @8
    cB
    wcel
    @26
    mapdpglem28.ue
    @33
    cB
    cA
    @5
    @7
    @4
    mapdpglem26.b
    @34
    ringcl
    syl3anc
    @23
    eleqtrrd
    wph
    vv
    vu
    cA
    cB
    cC
    cR
    c.x
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    cO
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    mapdpg.k
    mapdpg.x
    mapdpg.y
    mapdpg.g
    mapdpg.ne
    mapdpg.e
    mapdpgem25.h1
    mapdpgem25.i1
    mapdpglem26.a
    mapdpglem26.b
    mapdpglem26.t
    mapdpglem26.o
    mapdpglem28.ve
    mapdpglem28.u1
    mapdpglem28.u2
    mapdpglem29
    wph
    @1
    cG
    c.x
    co
    #
    @8
    @14
    c.x
    co
    #
    @11
    co
    @35
    @4
    @7
    @14
    c.x
    co
    #
    c.x
    co
    #
    @11
    co
    @35
    @37
    cR
    co
    #
    @0
    cG
    c.x
    co
    #
    @6
    @14
    c.x
    co
    #
    @11
    co
    #
    wph
    @36
    @38
    @35
    @11
    wph
    cC
    cA
    c.x
    @5
    cU
    cF
    @14
    cH
    cK
    cB
    cW
    @4
    @7
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    @34
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    @33
    mapdpglem28.ue
    @22
    lcdvsass
    oveq2d
    wph
    cC
    @11
    cA
    c.x
    cU
    @1
    @35
    @37
    cH
    cK
    cR
    @3
    cF
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    @32
    @30
    mapdpg.c
    mapdpg.f
    @16
    mapdpglem26.t
    mapdpg.r
    mapdpg.k
    wph
    cC
    cB
    cA
    c.x
    cU
    cG
    cH
    cK
    cF
    cW
    @1
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    @31
    mapdpg.g
    lcdvscl
    wph
    cC
    cB
    cA
    c.x
    cU
    @14
    cH
    cK
    cF
    cW
    @7
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    mapdpglem28.ue
    @22
    lcdvscl
    lcdvsub
    wph
    @42
    @40
    @4
    @0
    @14
    c.x
    co
    #
    c.x
    co
    #
    @11
    co
    @40
    @43
    cR
    co
    #
    @39
    wph
    @41
    @44
    @40
    @11
    wph
    cC
    cA
    c.x
    @5
    cU
    cF
    @14
    cH
    cK
    cB
    cW
    @4
    @0
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    @34
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    @33
    mapdpglem28.ve
    @22
    lcdvsass
    oveq2d
    wph
    cC
    @11
    cA
    c.x
    cU
    @1
    @40
    @43
    cH
    cK
    cR
    @3
    cF
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    @32
    @30
    mapdpg.c
    mapdpg.f
    @16
    mapdpglem26.t
    mapdpg.r
    mapdpg.k
    wph
    cC
    cB
    cA
    c.x
    cU
    cG
    cH
    cK
    cF
    cW
    @0
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    mapdpglem28.ve
    mapdpg.g
    lcdvscl
    wph
    cC
    cB
    cA
    c.x
    cU
    @14
    cH
    cK
    cF
    cW
    @0
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    mapdpglem26.b
    mapdpg.c
    mapdpg.f
    mapdpglem26.t
    mapdpg.k
    mapdpglem28.ve
    @22
    lcdvscl
    lcdvsub
    wph
    @45
    cG
    @37
    cR
    co
    @39
    wph
    vv
    vu
    cA
    cB
    cC
    cR
    c.x
    cU
    vh
    vi
    cF
    cG
    cH
    cJ
    cK
    cM
    c.mi
    cN
    cO
    cV
    cW
    cX
    cY
    c.0
    mapdpg.h
    mapdpg.m
    mapdpg.u
    mapdpg.v
    mapdpg.s
    mapdpg.z
    mapdpg.n
    mapdpg.c
    mapdpg.f
    mapdpg.r
    mapdpg.j
    mapdpg.k
    mapdpg.x
    mapdpg.y
    mapdpg.g
    mapdpg.ne
    mapdpg.e
    mapdpgem25.h1
    mapdpgem25.i1
    mapdpglem26.a
    mapdpglem26.b
    mapdpglem26.t
    mapdpglem26.o
    mapdpglem28.ve
    mapdpglem28.u1
    mapdpglem28.u2
    mapdpglem28
    wph
    @35
    cG
    @37
    cR
    wph
    @12
    cur
    cfv
    #
    cG
    c.x
    co
    #
    @35
    cG
    wph
    @46
    @1
    cG
    c.x
    wph
    cC
    @12
    cU
    @1
    cA
    cH
    @46
    cK
    cW
    mapdpg.h
    mapdpg.u
    mapdpglem26.a
    @30
    mapdpg.c
    @17
    @46
    eqid
    #
    mapdpg.k
    lcd1
    oveq1d
    wph
    cC
    clmod
    wcel
    @19
    @47
    cG
    wceq
    wph
    cC
    cH
    cK
    cW
    mapdpg.h
    mapdpg.c
    mapdpg.k
    lcdlmod
    mapdpg.g
    c.x
    @46
    @12
    cF
    cC
    cG
    mapdpg.f
    @17
    mapdpglem26.t
    @48
    lmodvs1
    syl2anc
    eqtr3d
    oveq1d
    eqtr4d
    3eqtr2rd
    3eqtr2rd
    lvecindp2
    wph
    @9
    @10
    @2
    wph
    @9
    @0
    @3
    cfv
    #
    @7
    @3
    cfv
    #
    wceq
    @10
    wph
    @6
    @49
    @8
    @50
    wph
    cB
    cA
    @5
    @1
    @3
    @0
    mapdpglem26.b
    @34
    @30
    @32
    @26
    mapdpglem28.ve
    rngnegr
    wph
    cB
    cA
    @5
    @1
    @3
    @7
    mapdpglem26.b
    @34
    @30
    @32
    @26
    mapdpglem28.ue
    rngnegr
    eqeq12d
    wph
    cB
    cA
    @3
    @0
    @7
    mapdpglem26.b
    @32
    @29
    mapdpglem28.ve
    mapdpglem28.ue
    grpinv11
    bitrd
    anbi2d
    mpbid
end
