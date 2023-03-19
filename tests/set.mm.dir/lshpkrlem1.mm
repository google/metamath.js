include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "wcel.mm"
include "cfv.mm"
include "wreu.mm"
include "wb.mm"
include "clmod.mm"
include "cgrp.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodfgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "lshpsmreu.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "riota2.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpr.mm"
include "eqidd.mm"
include "eqeq2.mm"
include "rspcev.mm"
include "ex.mm"
include "wi.mm"
include "eleq1a.mm"
include "a1i.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "c0g.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "adantr.mm"
include "clss.mm"
include "lshplss.mm"
include "lssel.mm"
include "sylan.mm"
include "lmod0vrid.mm"
include "eqtrd.mm"
include "bicomd.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "eqeq1.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "cbvrexv.mm"
include "riotabiia.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "3bitr4d.mm"

theorem lshpkrlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vb: setvar b
  assume lshpkrlem.v: |- V = ( Base ` W )
  assume lshpkrlem.a: |- .+ = ( +g ` W )
  assume lshpkrlem.n: |- N = ( LSpan ` W )
  assume lshpkrlem.p: |- .(+) = ( LSSum ` W )
  assume lshpkrlem.h: |- H = ( LSHyp ` W )
  assume lshpkrlem.w: |- ( ph -> W e. LVec )
  assume lshpkrlem.u: |- ( ph -> U e. H )
  assume lshpkrlem.z: |- ( ph -> Z e. V )
  assume lshpkrlem.x: |- ( ph -> X e. V )
  assume lshpkrlem.e: |- ( ph -> ( U .(+) ( N ` { Z } ) ) = V )
  assume lshpkrlem.d: |- D = ( Scalar ` W )
  assume lshpkrlem.k: |- K = ( Base ` D )
  assume lshpkrlem.t: |- .x. = ( .s ` W )
  assume lshpkrlem.o: |- .0. = ( 0g ` D )
  assume lshpkrlem.g: |- G = ( x e. V |-> ( iota_ k e. K E. y e. U x = ( y .+ ( k .x. Z ) ) ) )

  disjoint k x
  disjoint k y
  disjoint .+ k
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint K k
  disjoint K x
  disjoint .0. k
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint .+ b
  disjoint .0. b
  disjoint .x. b
  disjoint U b
  disjoint X b
  disjoint Z b
  disjoint b ph
  assert |- ( ph -> ( X e. U <-> ( G ` X ) = .0. ) )

  proof
    wph
    cX
    vb
    cv
    #
    c.0
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vb
    cU
    wrex
    #
    cX
    @0
    vk
    cv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vb
    cU
    wrex
    #
    vk
    cK
    crio
    #
    c.0
    wceq
    #
    cX
    cU
    wcel
    #
    cX
    cG
    cfv
    #
    c.0
    wceq
    wph
    c.0
    cK
    wcel
    #
    @9
    vk
    cK
    wreu
    @4
    @11
    wb
    wph
    cW
    clmod
    wcel
    #
    cD
    cgrp
    wcel
    @14
    wph
    cW
    clvec
    wcel
    #
    @15
    lshpkrlem.w
    cW
    lveclmod
    #
    syl
    #
    cD
    cW
    lshpkrlem.d
    lmodfgrp
    cK
    cD
    c.0
    lshpkrlem.k
    lshpkrlem.o
    grpidcl
    3syl
    wph
    vb
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    cH
    cK
    cN
    cV
    cW
    cX
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    lshpkrlem.w
    lshpkrlem.u
    lshpkrlem.z
    lshpkrlem.x
    lshpkrlem.e
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpsmreu
    @9
    @4
    vk
    cK
    c.0
    @5
    c.0
    wceq
    #
    @8
    @3
    vb
    cU
    @19
    @7
    @2
    cX
    @19
    @6
    @1
    @0
    c.pl
    @5
    c.0
    cZ
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    riota2
    syl2anc
    wph
    @12
    cX
    @0
    wceq
    #
    vb
    cU
    wrex
    #
    @4
    wph
    @12
    @21
    wph
    @12
    @21
    wph
    @12
    wa
    #
    @12
    cX
    cX
    wceq
    #
    @21
    wph
    @12
    simpr
    @22
    cX
    eqidd
    @20
    @23
    vb
    cX
    cU
    @0
    cX
    cX
    eqeq2
    rspcev
    syl2anc
    ex
    wph
    @20
    @12
    vb
    cU
    @0
    cU
    wcel
    #
    @20
    @12
    wi
    wi
    wph
    @0
    cU
    cX
    eleq1a
    a1i
    rexlimdv
    impbid
    wph
    @20
    @3
    vb
    cU
    wph
    @24
    wa
    #
    @3
    @20
    @25
    @2
    @0
    cX
    @25
    @2
    @0
    cW
    c0g
    cfv
    #
    c.pl
    co
    #
    @0
    @25
    @1
    @26
    @0
    c.pl
    wph
    @1
    @26
    wceq
    #
    @24
    wph
    @15
    cZ
    cV
    wcel
    @28
    @18
    lshpkrlem.z
    c.x
    cD
    c.0
    cV
    cW
    cZ
    @26
    lshpkrlem.v
    lshpkrlem.d
    lshpkrlem.t
    lshpkrlem.o
    @26
    eqid
    #
    lmod0vs
    syl2anc
    adantr
    oveq2d
    @25
    @15
    @0
    cV
    wcel
    #
    @27
    @0
    wceq
    @25
    @16
    @15
    wph
    @16
    @24
    lshpkrlem.w
    adantr
    @17
    syl
    wph
    cU
    cW
    clss
    cfv
    #
    wcel
    @24
    @30
    wph
    @31
    cU
    cH
    cW
    @31
    eqid
    #
    lshpkrlem.h
    @18
    lshpkrlem.u
    lshplss
    @31
    cU
    cV
    cW
    @0
    lshpkrlem.v
    @32
    lssel
    sylan
    c.pl
    cV
    cW
    @0
    @26
    lshpkrlem.v
    lshpkrlem.a
    @29
    lmod0vrid
    syl2anc
    eqtrd
    eqeq2d
    bicomd
    rexbidva
    bitrd
    wph
    @13
    @10
    c.0
    wph
    cX
    cV
    wcel
    #
    @13
    @10
    wceq
    lshpkrlem.x
    @33
    @13
    cX
    vy
    cv
    #
    @6
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    crio
    #
    @10
    vx
    cX
    vx
    cv
    #
    @35
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    crio
    @38
    cV
    cG
    @39
    cX
    wceq
    #
    @41
    @37
    vk
    cK
    @42
    @40
    @36
    vy
    cU
    @39
    cX
    @35
    eqeq1
    rexbidv
    riotabidv
    lshpkrlem.g
    @37
    vk
    cK
    riotaex
    fvmpt
    @37
    @9
    vk
    cK
    @37
    @9
    wb
    @5
    cK
    wcel
    @36
    @8
    vy
    vb
    cU
    @34
    @0
    wceq
    @35
    @7
    cX
    @34
    @0
    @6
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    a1i
    riotabiia
    syl6eq
    syl
    eqeq1d
    3bitr4d
end
