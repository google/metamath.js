include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "rphalfcld.mm"
include "cngp.mm"
include "cr.mm"
include "cnlm.mm"
include "ccph.mm"
include "cphnlm.mm"
include "syl.mm"
include "nlmngp.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "cc0.mm"
include "nmge0.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
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
include "ipcnlem2.mm"
include "expr.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"

theorem ipcnlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cT: class T
  let cU: class U
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume ipcn.v: |- V = ( Base ` W )
  assume ipcn.h: |- ., = ( .i ` W )
  assume ipcn.d: |- D = ( dist ` W )
  assume ipcn.n: |- N = ( norm ` W )
  assume ipcn.t: |- T = ( ( R / 2 ) / ( ( N ` A ) + 1 ) )
  assume ipcn.u: |- U = ( ( R / 2 ) / ( ( N ` B ) + T ) )
  assume ipcn.w: |- ( ph -> W e. CPreHil )
  assume ipcn.a: |- ( ph -> A e. V )
  assume ipcn.b: |- ( ph -> B e. V )
  assume ipcn.r: |- ( ph -> R e. RR+ )

  disjoint A r
  disjoint B r
  disjoint D r
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
  disjoint ., r
  disjoint R r
  disjoint V r
  disjoint V y
  assert |- ( ph -> E. r e. RR+ A. x e. V A. y e. V ( ( ( A D x ) < r /\ ( B D y ) < r ) -> ( abs ` ( ( A ., B ) - ( x ., y ) ) ) < R ) )

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
    cA
    vx
    cv
    #
    cD
    co
    #
    @1
    clt
    wbr
    #
    cB
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
    cA
    cB
    c.xi
    co
    @3
    @6
    c.xi
    co
    cmin
    co
    cabs
    cfv
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
    cV
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
    cV
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
    cA
    cN
    cfv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    crp
    ipcn.t
    wph
    @19
    @21
    wph
    cR
    ipcn.r
    rphalfcld
    #
    wph
    @20
    wph
    cW
    cngp
    wcel
    #
    cA
    cV
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
    wph
    cW
    ccph
    wcel
    #
    @25
    ipcn.w
    cW
    cphnlm
    syl
    cW
    nlmngp
    syl
    #
    ipcn.a
    cA
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmcl
    syl2anc
    wph
    @23
    @24
    cc0
    @20
    cle
    wbr
    @27
    ipcn.a
    cA
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmge0
    syl2anc
    ge0p1rpd
    rpdivcld
    syl5eqel
    #
    wph
    cU
    @19
    cB
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
    ipcn.u
    wph
    @19
    @30
    @22
    wph
    @30
    wph
    @29
    cT
    wph
    @23
    cB
    cV
    wcel
    #
    @29
    cr
    wcel
    @27
    ipcn.b
    cB
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmcl
    syl2anc
    #
    wph
    cT
    @28
    rpred
    #
    readdcld
    #
    wph
    cc0
    @29
    @30
    wph
    0red
    @32
    @34
    wph
    @23
    @31
    cc0
    @29
    cle
    wbr
    @27
    ipcn.b
    cB
    cW
    cN
    cV
    ipcn.v
    ipcn.n
    nmge0
    syl2anc
    wph
    @29
    cT
    @32
    @28
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
    cV
    cV
    wph
    @3
    cV
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
    @39
    @9
    wa
    #
    wa
    #
    cA
    cB
    cD
    cR
    cT
    cU
    c.xi
    cN
    cV
    cW
    @3
    @6
    ipcn.v
    ipcn.h
    ipcn.d
    ipcn.n
    ipcn.t
    ipcn.u
    wph
    @26
    @40
    ipcn.w
    adantr
    wph
    @24
    @40
    ipcn.a
    adantr
    #
    wph
    @31
    @40
    ipcn.b
    adantr
    #
    wph
    cR
    crp
    wcel
    @40
    ipcn.r
    adantr
    wph
    @37
    @38
    @9
    simprll
    #
    wph
    @37
    @38
    @9
    simprlr
    #
    @41
    @4
    @1
    cU
    @41
    cW
    cmt
    wcel
    #
    @24
    @37
    @4
    cr
    wcel
    @41
    @23
    @46
    wph
    @23
    @40
    @27
    adantr
    cW
    ngpms
    #
    syl
    @42
    @44
    cA
    @3
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    mscl
    syl3anc
    @41
    @1
    wph
    @2
    @40
    @36
    adantr
    rpred
    #
    wph
    cU
    cr
    wcel
    #
    @40
    wph
    cU
    @35
    rpred
    adantr
    #
    wph
    @39
    @5
    @8
    simprrl
    @41
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
    @40
    @33
    adantr
    #
    @50
    cT
    cU
    min2
    syl2anc
    ltletrd
    @41
    @7
    @1
    cT
    @41
    @46
    @31
    @38
    @7
    cr
    wcel
    wph
    @46
    @40
    wph
    @23
    @46
    @27
    @47
    syl
    adantr
    @43
    @45
    cB
    @6
    cD
    cW
    cV
    ipcn.v
    ipcn.d
    mscl
    syl3anc
    @48
    @52
    wph
    @39
    @5
    @8
    simprrr
    @41
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
    ipcnlem2
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
    cV
    cV
    @53
    @16
    @9
    @10
    @53
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
