include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "c2.mm"
include "cdiv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "rphalfcld.mm"
include "cngp.mm"
include "cr.mm"
include "cnlm.mm"
include "nlmngp2.mm"
include "syl.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "nmge0.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "nlmngp.mm"
include "rpred.mm"
include "readdcld.mm"
include "0red.mm"
include "ltaddrpd.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "ifcld.mm"
include "adantr.mm"
include "simprll.mm"
include "simprlr.mm"
include "cmt.mm"
include "ngpms.mm"
include "mscl.mm"
include "syl3anc.mm"
include "simprrl.mm"
include "min2.mm"
include "ltletrd.mm"
include "simprrr.mm"
include "min1.mm"
include "nlmvscnlem2.mm"
include "expr.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"

theorem nlmvscnlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  assume nlmvscn.f: |- F = ( Scalar ` W )
  assume nlmvscn.v: |- V = ( Base ` W )
  assume nlmvscn.k: |- K = ( Base ` F )
  assume nlmvscn.d: |- D = ( dist ` W )
  assume nlmvscn.e: |- E = ( dist ` F )
  assume nlmvscn.n: |- N = ( norm ` W )
  assume nlmvscn.a: |- A = ( norm ` F )
  assume nlmvscn.s: |- .x. = ( .s ` W )
  assume nlmvscn.t: |- T = ( ( R / 2 ) / ( ( A ` B ) + 1 ) )
  assume nlmvscn.u: |- U = ( ( R / 2 ) / ( ( N ` X ) + T ) )
  assume nlmvscn.w: |- ( ph -> W e. NrmMod )
  assume nlmvscn.r: |- ( ph -> R e. RR+ )
  assume nlmvscn.b: |- ( ph -> B e. K )
  assume nlmvscn.x: |- ( ph -> X e. V )

  disjoint B r
  disjoint D r
  disjoint E r
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint r x
  disjoint r y
  disjoint T r
  disjoint T x
  disjoint T y
  disjoint U r
  disjoint U x
  disjoint U y
  disjoint F r
  disjoint F x
  disjoint F y
  disjoint K r
  disjoint K y
  disjoint R r
  disjoint V r
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  disjoint X r
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint W s
  disjoint W w
  disjoint W z
  disjoint .x. s
  disjoint .x. w
  disjoint .x. z
  assert |- ( ph -> E. r e. RR+ A. x e. K A. y e. V ( ( ( B E x ) < r /\ ( X D y ) < r ) -> ( ( B .x. X ) D ( x .x. y ) ) < R ) )

  proof
    wph
    cT
    cU
    cle
    wbr
    #
    cT
    cU
    cif
    #
    crp
    wcel
    #
    cB
    vx
    cv
    #
    cE
    co
    #
    @1
    clt
    wbr
    #
    cX
    vy
    cv
    #
    cD
    co
    #
    @1
    clt
    wbr
    #
    wa
    #
    cB
    cX
    c.x
    co
    @3
    @6
    c.x
    co
    cD
    co
    cR
    clt
    wbr
    #
    wi
    #
    vy
    cV
    wral
    vx
    cK
    wral
    #
    @4
    vr
    cv
    #
    clt
    wbr
    #
    @7
    @13
    clt
    wbr
    #
    wa
    #
    @10
    wi
    #
    vy
    cV
    wral
    vx
    cK
    wral
    #
    vr
    crp
    wrex
    wph
    @0
    cT
    cU
    crp
    wph
    cT
    cR
    c2
    cdiv
    co
    #
    cB
    cA
    cfv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    crp
    nlmvscn.t
    wph
    @19
    @21
    wph
    cR
    nlmvscn.r
    rphalfcld
    #
    wph
    @20
    wph
    cF
    cngp
    wcel
    #
    cB
    cK
    wcel
    #
    @20
    cr
    wcel
    wph
    cW
    cnlm
    wcel
    #
    @23
    nlmvscn.w
    cF
    cW
    nlmvscn.f
    nlmngp2
    syl
    #
    nlmvscn.b
    cB
    cF
    cA
    cK
    nlmvscn.k
    nlmvscn.a
    nmcl
    syl2anc
    wph
    @23
    @24
    cc0
    @20
    cle
    wbr
    @26
    nlmvscn.b
    cB
    cF
    cA
    cK
    nlmvscn.k
    nlmvscn.a
    nmge0
    syl2anc
    ge0p1rpd
    rpdivcld
    syl5eqel
    #
    wph
    cU
    @19
    cX
    cN
    cfv
    #
    cT
    caddc
    co
    #
    cdiv
    co
    crp
    nlmvscn.u
    wph
    @19
    @29
    @22
    wph
    @29
    wph
    @28
    cT
    wph
    cW
    cngp
    wcel
    #
    cX
    cV
    wcel
    #
    @28
    cr
    wcel
    wph
    @25
    @30
    nlmvscn.w
    cW
    nlmngp
    syl
    #
    nlmvscn.x
    cX
    cW
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    nmcl
    syl2anc
    #
    wph
    cT
    @27
    rpred
    #
    readdcld
    #
    wph
    cc0
    @28
    @29
    wph
    0red
    @33
    @35
    wph
    @30
    @31
    cc0
    @28
    cle
    wbr
    @32
    nlmvscn.x
    cX
    cW
    cN
    cV
    nlmvscn.v
    nlmvscn.n
    nmge0
    syl2anc
    wph
    @28
    cT
    @33
    @27
    ltaddrpd
    lelttrd
    elrpd
    rpdivcld
    syl5eqel
    #
    ifcld
    #
    wph
    @11
    vx
    vy
    cK
    cV
    wph
    @3
    cK
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    @9
    @10
    wph
    @40
    @9
    wa
    #
    wa
    #
    cA
    cB
    @3
    cD
    cR
    cT
    c.x
    cU
    cE
    cF
    cK
    cN
    cV
    cW
    cX
    @6
    nlmvscn.f
    nlmvscn.v
    nlmvscn.k
    nlmvscn.d
    nlmvscn.e
    nlmvscn.n
    nlmvscn.a
    nlmvscn.s
    nlmvscn.t
    nlmvscn.u
    wph
    @25
    @41
    nlmvscn.w
    adantr
    wph
    cR
    crp
    wcel
    @41
    nlmvscn.r
    adantr
    wph
    @24
    @41
    nlmvscn.b
    adantr
    #
    wph
    @31
    @41
    nlmvscn.x
    adantr
    #
    wph
    @38
    @39
    @9
    simprll
    #
    wph
    @38
    @39
    @9
    simprlr
    #
    @42
    @4
    @1
    cU
    @42
    cF
    cmt
    wcel
    #
    @24
    @38
    @4
    cr
    wcel
    @42
    @23
    @47
    wph
    @23
    @41
    @26
    adantr
    cF
    ngpms
    syl
    @43
    @45
    cB
    @3
    cE
    cF
    cK
    nlmvscn.k
    nlmvscn.e
    mscl
    syl3anc
    @42
    @1
    wph
    @2
    @41
    @37
    adantr
    rpred
    #
    wph
    cU
    cr
    wcel
    #
    @41
    wph
    cU
    @36
    rpred
    adantr
    #
    wph
    @40
    @5
    @8
    simprrl
    @42
    cT
    cr
    wcel
    #
    @49
    @1
    cU
    cle
    wbr
    wph
    @51
    @41
    @34
    adantr
    #
    @50
    cT
    cU
    min2
    syl2anc
    ltletrd
    @42
    @7
    @1
    cT
    @42
    cW
    cmt
    wcel
    #
    @31
    @39
    @7
    cr
    wcel
    wph
    @53
    @41
    wph
    @30
    @53
    @32
    cW
    ngpms
    syl
    adantr
    @44
    @46
    cX
    @6
    cD
    cW
    cV
    nlmvscn.v
    nlmvscn.d
    mscl
    syl3anc
    @48
    @52
    wph
    @40
    @5
    @8
    simprrr
    @42
    @51
    @49
    @1
    cT
    cle
    wbr
    @52
    @50
    cT
    cU
    min1
    syl2anc
    ltletrd
    nlmvscnlem2
    expr
    ralrimivva
    @18
    @12
    vr
    @1
    crp
    @13
    @1
    wceq
    #
    @17
    @11
    vx
    vy
    cK
    cV
    @54
    @16
    @9
    @10
    @54
    @14
    @5
    @15
    @8
    @13
    @1
    @4
    clt
    breq2
    @13
    @1
    @7
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
end
