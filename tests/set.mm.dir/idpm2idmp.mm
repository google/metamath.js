include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "pmatring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "pm2mpfval.mm"
include "mpd3an3.mm"
include "decpmatid.mm"
include "3expa.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "csb.mm"
include "ovif.mm"
include "csca.mm"
include "matring.mm"
include "ply1sca.mm"
include "adantr.mm"
include "fveq2d.mm"
include "clmod.mm"
include "cbs.mm"
include "ply1lmod.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "lmod0vs.mm"
include "ifeq12d.mm"
include "syl5eq.mm"
include "cvv.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmnd.mm"
include "3syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "0nn0.mm"
include "ralrimiva.mm"
include "gsummpt1n0.mm"
include "c0ex.mm"
include "csbov1g.mm"
include "mp1i.mm"
include "csbvarg.mm"
include "ply1idvr1.mm"
include "3eqtrd.mm"

theorem idpm2idmp
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let c.ex: class .^
  let c.as: class .*
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vk: setvar k
  let cV: class V
  let va: setvar a
  let vq: setvar q
  let cM: class M
  let cK: class K
  assume pm2mpval.p: |- P = ( Poly1 ` R )
  assume pm2mpval.c: |- C = ( N Mat P )
  assume pm2mpval.b: |- B = ( Base ` C )
  assume pm2mpval.m: |- .* = ( .s ` Q )
  assume pm2mpval.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpval.x: |- X = ( var1 ` A )
  assume pm2mpval.a: |- A = ( N Mat R )
  assume pm2mpval.q: |- Q = ( Poly1 ` A )
  assume pm2mpval.t: |- T = ( N pMatToMatPoly R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( T ` ( 1r ` C ) ) = ( 1r ` Q ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cur
    cfv
    #
    cT
    cfv
    #
    cQ
    vk
    cn0
    @3
    vk
    cv
    #
    cdecpmat
    co
    #
    @5
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cQ
    vk
    cn0
    @5
    cc0
    wceq
    #
    cA
    cur
    cfv
    #
    cA
    c0g
    cfv
    #
    cif
    #
    @7
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cQ
    cur
    cfv
    #
    @0
    @1
    @3
    cB
    wcel
    #
    @4
    @10
    wceq
    @2
    cC
    crg
    wcel
    @19
    cC
    cP
    cR
    cN
    pm2mpval.p
    pm2mpval.c
    pmatring
    cB
    cC
    @3
    pm2mpval.b
    @3
    eqid
    #
    ringidcl
    syl
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    vk
    c.ex
    c.as
    @3
    cN
    crg
    cX
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.m
    pm2mpval.e
    pm2mpval.x
    pm2mpval.a
    pm2mpval.q
    pm2mpval.t
    pm2mpfval
    mpd3an3
    @2
    @9
    @16
    cQ
    cgsu
    @2
    vk
    cn0
    @8
    @15
    @2
    @5
    cn0
    wcel
    #
    wa
    #
    @6
    @14
    @7
    c.as
    @0
    @1
    @21
    @6
    @14
    wceq
    cA
    cC
    cP
    cR
    @12
    @3
    @5
    cN
    @13
    pm2mpval.p
    pm2mpval.c
    @20
    pm2mpval.a
    @13
    eqid
    @12
    eqid
    decpmatid
    3expa
    oveq1d
    mpteq2dva
    oveq2d
    @2
    @17
    cQ
    vk
    cn0
    @11
    @7
    cQ
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cgsu
    co
    vk
    cc0
    @7
    csb
    #
    @18
    @2
    @16
    @25
    cQ
    cgsu
    @2
    vk
    cn0
    @15
    @24
    @22
    @15
    @11
    @12
    @7
    c.as
    co
    #
    @13
    @7
    c.as
    co
    #
    cif
    @24
    @11
    @12
    @13
    @7
    c.as
    ovif
    @22
    @11
    @27
    @7
    @28
    @23
    @22
    @27
    cQ
    csca
    cfv
    #
    cur
    cfv
    #
    @7
    c.as
    co
    #
    @7
    @22
    @12
    @30
    @7
    c.as
    @22
    cA
    @29
    cur
    @2
    cA
    @29
    wceq
    #
    @21
    @2
    cA
    crg
    wcel
    #
    @32
    cA
    cR
    cN
    pm2mpval.a
    matring
    #
    cQ
    cA
    crg
    pm2mpval.q
    ply1sca
    syl
    adantr
    #
    fveq2d
    oveq1d
    @22
    cQ
    clmod
    wcel
    #
    @7
    cQ
    cbs
    cfv
    #
    wcel
    #
    @31
    @7
    wceq
    @2
    @36
    @21
    @2
    @33
    @36
    @34
    cQ
    cA
    pm2mpval.q
    ply1lmod
    syl
    adantr
    #
    @2
    @33
    @21
    @38
    @34
    @37
    @5
    cQ
    cA
    c.ex
    cQ
    cmgp
    cfv
    #
    cX
    pm2mpval.q
    pm2mpval.x
    @40
    eqid
    #
    pm2mpval.e
    @37
    eqid
    #
    ply1moncl
    sylan
    #
    c.as
    @30
    @29
    @37
    cQ
    @7
    @42
    @29
    eqid
    #
    pm2mpval.m
    @30
    eqid
    lmodvs1
    syl2anc
    eqtrd
    @22
    @28
    @29
    c0g
    cfv
    #
    @7
    c.as
    co
    #
    @23
    @22
    @13
    @45
    @7
    c.as
    @22
    cA
    @29
    c0g
    @35
    fveq2d
    oveq1d
    @22
    @36
    @38
    @46
    @23
    wceq
    @39
    @43
    c.as
    @29
    @45
    @37
    cQ
    @7
    @23
    @42
    @44
    pm2mpval.m
    @45
    eqid
    @23
    eqid
    #
    lmod0vs
    syl2anc
    eqtrd
    ifeq12d
    syl5eq
    mpteq2dva
    oveq2d
    @2
    @7
    vk
    @25
    cQ
    cn0
    cvv
    cc0
    @23
    @47
    @2
    @33
    cQ
    crg
    wcel
    cQ
    cmnd
    wcel
    @34
    cQ
    cA
    pm2mpval.q
    ply1ring
    cQ
    ringmnd
    3syl
    cn0
    cvv
    wcel
    @2
    nn0ex
    a1i
    cc0
    cn0
    wcel
    @2
    0nn0
    a1i
    @25
    eqid
    @2
    @38
    vk
    cn0
    @43
    ralrimiva
    gsummpt1n0
    @2
    @26
    vk
    cc0
    @5
    csb
    #
    cX
    c.ex
    co
    #
    cc0
    cX
    c.ex
    co
    #
    @18
    cc0
    cvv
    wcel
    #
    @26
    @49
    wceq
    @2
    c0ex
    vk
    cc0
    @5
    cX
    c.ex
    cvv
    csbov1g
    mp1i
    @2
    @48
    cc0
    cX
    c.ex
    @51
    @48
    cc0
    wceq
    @2
    c0ex
    vk
    cc0
    cvv
    csbvarg
    mp1i
    oveq1d
    @2
    @33
    @50
    @18
    wceq
    @34
    cQ
    cA
    c.ex
    @40
    cX
    pm2mpval.q
    pm2mpval.x
    @41
    pm2mpval.e
    ply1idvr1
    syl
    3eqtrd
    3eqtrd
    3eqtrd
end
