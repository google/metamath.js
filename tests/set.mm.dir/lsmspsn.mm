include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "csubg.mm"
include "wb.mm"
include "clmod.mm"
include "lspsnsubg.mm"
include "syl2anc.mm"
include "lsmelval.mm"
include "lspsnel.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "biantrurd.mm"
include "r19.41v.mm"
include "rexbii.mm"
include "reeanv.mm"
include "anbi1i.mm"
include "3bitrri.mm"
include "syl6bb.mm"
include "2rexbidva.mm"
include "rexrot4.mm"
include "adantr.mm"
include "simprl.mm"
include "lspsneli.mm"
include "simprr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "ceqsrex2v.mm"
include "3bitrd.mm"

theorem lsmspsn
  let wph: wff ph
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vw: setvar w
  assume lsmspsn.v: |- V = ( Base ` W )
  assume lsmspsn.a: |- .+ = ( +g ` W )
  assume lsmspsn.f: |- F = ( Scalar ` W )
  assume lsmspsn.k: |- K = ( Base ` F )
  assume lsmspsn.t: |- .x. = ( .s ` W )
  assume lsmspsn.p: |- .(+) = ( LSSum ` W )
  assume lsmspsn.n: |- N = ( LSpan ` W )
  assume lsmspsn.w: |- ( ph -> W e. LMod )
  assume lsmspsn.x: |- ( ph -> X e. V )
  assume lsmspsn.y: |- ( ph -> Y e. V )

  disjoint j k
  disjoint .+ j
  disjoint .+ k
  disjoint F j
  disjoint F k
  disjoint K j
  disjoint K k
  disjoint N j
  disjoint N k
  disjoint .x. j
  disjoint .x. k
  disjoint U j
  disjoint U k
  disjoint V j
  disjoint V k
  disjoint W j
  disjoint W k
  disjoint X j
  disjoint X k
  disjoint Y j
  disjoint Y k
  disjoint j ph
  disjoint k ph
  disjoint j v
  disjoint j w
  disjoint k v
  disjoint k w
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint K v
  disjoint K w
  disjoint N v
  disjoint N w
  disjoint .x. v
  disjoint .x. w
  disjoint U v
  disjoint U w
  disjoint W v
  disjoint W w
  disjoint X v
  disjoint X w
  disjoint Y v
  disjoint Y w
  disjoint ph v
  disjoint ph w
  assert |- ( ph -> ( U e. ( ( N ` { X } ) .(+) ( N ` { Y } ) ) <-> E. j e. K E. k e. K U = ( ( j .x. X ) .+ ( k .x. Y ) ) ) )

  proof
    wph
    cU
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    c.po
    co
    wcel
    #
    cU
    vv
    cv
    #
    vw
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @1
    wrex
    vv
    @0
    wrex
    #
    @3
    vj
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    @4
    vk
    cv
    #
    cY
    c.x
    co
    #
    wceq
    #
    wa
    #
    @6
    wa
    #
    vw
    @1
    wrex
    vv
    @0
    wrex
    #
    vk
    cK
    wrex
    vj
    cK
    wrex
    #
    cU
    @9
    @12
    c.pl
    co
    #
    wceq
    #
    vk
    cK
    wrex
    vj
    cK
    wrex
    wph
    @0
    cW
    csubg
    cfv
    #
    wcel
    #
    @1
    @20
    wcel
    #
    @2
    @7
    wb
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @21
    lsmspsn.w
    lsmspsn.x
    cN
    cV
    cW
    cX
    lsmspsn.v
    lsmspsn.n
    lspsnsubg
    syl2anc
    wph
    @23
    cY
    cV
    wcel
    #
    @22
    lsmspsn.w
    lsmspsn.y
    cN
    cV
    cW
    cY
    lsmspsn.v
    lsmspsn.n
    lspsnsubg
    syl2anc
    vv
    vw
    c.pl
    c.po
    @0
    @1
    cW
    cU
    lsmspsn.a
    lsmspsn.p
    lsmelval
    syl2anc
    wph
    @7
    @15
    vk
    cK
    wrex
    #
    vj
    cK
    wrex
    #
    vw
    @1
    wrex
    vv
    @0
    wrex
    @17
    wph
    @6
    @27
    vv
    vw
    @0
    @1
    wph
    @3
    @0
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    wa
    #
    @6
    @10
    vj
    cK
    wrex
    #
    @13
    vk
    cK
    wrex
    #
    wa
    #
    @6
    wa
    #
    @27
    @31
    @34
    @6
    wph
    @30
    @34
    wph
    @28
    @32
    @29
    @33
    wph
    @23
    @24
    @28
    @32
    wb
    lsmspsn.w
    lsmspsn.x
    c.x
    @3
    vj
    cF
    cK
    cN
    cV
    cW
    cX
    lsmspsn.f
    lsmspsn.k
    lsmspsn.v
    lsmspsn.t
    lsmspsn.n
    lspsnel
    syl2anc
    wph
    @23
    @25
    @29
    @33
    wb
    lsmspsn.w
    lsmspsn.y
    c.x
    @4
    vk
    cF
    cK
    cN
    cV
    cW
    cY
    lsmspsn.f
    lsmspsn.k
    lsmspsn.v
    lsmspsn.t
    lsmspsn.n
    lspsnel
    syl2anc
    anbi12d
    biimpa
    biantrurd
    @27
    @14
    vk
    cK
    wrex
    #
    @6
    wa
    #
    vj
    cK
    wrex
    @36
    vj
    cK
    wrex
    #
    @6
    wa
    @35
    @26
    @37
    vj
    cK
    @14
    @6
    vk
    cK
    r19.41v
    rexbii
    @36
    @6
    vj
    cK
    r19.41v
    @38
    @34
    @6
    @10
    @13
    vj
    vk
    cK
    cK
    reeanv
    anbi1i
    3bitrri
    syl6bb
    2rexbidva
    @15
    vv
    vw
    vj
    vk
    @0
    @1
    cK
    cK
    rexrot4
    syl6bb
    wph
    @16
    @19
    vj
    vk
    cK
    cK
    wph
    @8
    cK
    wcel
    #
    @11
    cK
    wcel
    #
    wa
    #
    wa
    #
    @9
    @0
    wcel
    @12
    @1
    wcel
    @16
    @19
    wb
    @42
    @8
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lsmspsn.v
    lsmspsn.t
    lsmspsn.f
    lsmspsn.k
    lsmspsn.n
    wph
    @23
    @41
    lsmspsn.w
    adantr
    #
    wph
    @39
    @40
    simprl
    wph
    @24
    @41
    lsmspsn.x
    adantr
    lspsneli
    @42
    @11
    c.x
    cF
    cK
    cN
    cV
    cW
    cY
    lsmspsn.v
    lsmspsn.t
    lsmspsn.f
    lsmspsn.k
    lsmspsn.n
    @43
    wph
    @39
    @40
    simprr
    wph
    @25
    @41
    lsmspsn.y
    adantr
    lspsneli
    @6
    cU
    @9
    @4
    c.pl
    co
    #
    wceq
    @19
    vv
    vw
    @9
    @12
    @0
    @1
    @10
    @5
    @44
    cU
    @3
    @9
    @4
    c.pl
    oveq1
    eqeq2d
    @13
    @44
    @18
    cU
    @4
    @12
    @9
    c.pl
    oveq2
    eqeq2d
    ceqsrex2v
    syl2anc
    2rexbidva
    3bitrd
end
