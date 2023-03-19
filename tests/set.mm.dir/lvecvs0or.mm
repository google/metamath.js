include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cinvr.mm"
include "cfv.mm"
include "oveq2.mm"
include "ad2antlr.mm"
include "cmulr.mm"
include "cur.mm"
include "cdr.mm"
include "wcel.mm"
include "clvec.mm"
include "adantr.mm"
include "lvecdrng.mm"
include "syl.mm"
include "simpr.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "clmod.mm"
include "lveclmod.mm"
include "drnginvrcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "adantlr.mm"
include "lmodvs0.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "lmod0vs.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "impbid.mm"

theorem lvecvs0or
  let wph: wff ph
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lvecmul0or.v: |- V = ( Base ` W )
  assume lvecmul0or.s: |- .x. = ( .s ` W )
  assume lvecmul0or.f: |- F = ( Scalar ` W )
  assume lvecmul0or.k: |- K = ( Base ` F )
  assume lvecmul0or.o: |- O = ( 0g ` F )
  assume lvecmul0or.z: |- .0. = ( 0g ` W )
  assume lvecmul0or.w: |- ( ph -> W e. LVec )
  assume lvecmul0or.a: |- ( ph -> A e. K )
  assume lvecmul0or.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( A .x. X ) = .0. <-> ( A = O \/ X = .0. ) ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    c.0
    wceq
    #
    cA
    cO
    wceq
    #
    cX
    c.0
    wceq
    #
    wo
    #
    wph
    @1
    @4
    wph
    @1
    wa
    #
    @2
    @3
    @2
    wn
    cA
    cO
    wne
    #
    @5
    @3
    cA
    cO
    df-ne
    @5
    @6
    @3
    @5
    @6
    wa
    #
    cA
    cF
    cinvr
    cfv
    #
    cfv
    #
    @0
    c.x
    co
    #
    @9
    c.0
    c.x
    co
    #
    cX
    c.0
    @1
    @10
    @11
    wceq
    wph
    @6
    @0
    c.0
    @9
    c.x
    oveq2
    ad2antlr
    wph
    @6
    @10
    cX
    wceq
    @1
    wph
    @6
    wa
    #
    @9
    cA
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    #
    @10
    cX
    @12
    @14
    @16
    cX
    c.x
    @12
    cF
    cdr
    wcel
    #
    cA
    cK
    wcel
    #
    @6
    @14
    @16
    wceq
    @12
    cW
    clvec
    wcel
    #
    @18
    wph
    @20
    @6
    lvecmul0or.w
    adantr
    cF
    cW
    lvecmul0or.f
    lvecdrng
    syl
    #
    wph
    @19
    @6
    lvecmul0or.a
    adantr
    #
    wph
    @6
    simpr
    #
    cK
    cF
    @13
    @16
    @8
    cA
    cO
    lvecmul0or.k
    lvecmul0or.o
    @13
    eqid
    #
    @16
    eqid
    #
    @8
    eqid
    #
    drnginvrl
    syl3anc
    oveq1d
    @12
    cW
    clmod
    wcel
    #
    @9
    cK
    wcel
    #
    @19
    cX
    cV
    wcel
    #
    @15
    @10
    wceq
    wph
    @27
    @6
    wph
    @20
    @27
    lvecmul0or.w
    cW
    lveclmod
    syl
    #
    adantr
    @12
    @18
    @19
    @6
    @28
    @21
    @22
    @23
    cK
    cF
    @8
    cA
    cO
    lvecmul0or.k
    lvecmul0or.o
    @26
    drnginvrcl
    syl3anc
    #
    @22
    wph
    @29
    @6
    lvecmul0or.x
    adantr
    @9
    cA
    c.x
    @13
    cF
    cK
    cV
    cW
    cX
    lvecmul0or.v
    lvecmul0or.f
    lvecmul0or.s
    lvecmul0or.k
    @24
    lmodvsass
    syl13anc
    wph
    @17
    cX
    wceq
    #
    @6
    wph
    @27
    @29
    @32
    @30
    lvecmul0or.x
    c.x
    @16
    cF
    cV
    cW
    cX
    lvecmul0or.v
    lvecmul0or.f
    lvecmul0or.s
    @25
    lmodvs1
    syl2anc
    adantr
    3eqtr3d
    adantlr
    @7
    @27
    @28
    @11
    c.0
    wceq
    @5
    @27
    @6
    wph
    @27
    @1
    @30
    adantr
    adantr
    wph
    @6
    @28
    @1
    @31
    adantlr
    c.x
    cF
    cK
    cW
    @9
    c.0
    lvecmul0or.f
    lvecmul0or.s
    lvecmul0or.k
    lvecmul0or.z
    lmodvs0
    syl2anc
    3eqtr3d
    ex
    syl5bir
    orrd
    ex
    wph
    @2
    @1
    @3
    wph
    @1
    @2
    cO
    cX
    c.x
    co
    #
    c.0
    wceq
    #
    wph
    @27
    @29
    @34
    @30
    lvecmul0or.x
    c.x
    cF
    cO
    cV
    cW
    cX
    c.0
    lvecmul0or.v
    lvecmul0or.f
    lvecmul0or.s
    lvecmul0or.o
    lvecmul0or.z
    lmod0vs
    syl2anc
    @2
    @0
    @33
    c.0
    cA
    cO
    cX
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    wph
    @1
    @3
    cA
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    wph
    @27
    @19
    @36
    @30
    lvecmul0or.a
    c.x
    cF
    cK
    cW
    cA
    c.0
    lvecmul0or.f
    lvecmul0or.s
    lvecmul0or.k
    lvecmul0or.z
    lmodvs0
    syl2anc
    @3
    @0
    @35
    c.0
    cX
    c.0
    cA
    c.x
    oveq2
    eqeq1d
    syl5ibrcom
    jaod
    impbid
end
