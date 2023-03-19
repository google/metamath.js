include "cfv.mm"
include "cv1.mm"
include "ce1.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "subrgvr1.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "c1o.mm"
include "ces.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cevl.mm"
include "c0.mm"
include "cmvr.mm"
include "con0.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "0lt1o.mm"
include "evlsvarsrng.mm"
include "vr1val.mm"
include "subrgmvr.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "3eqtr4d.mm"
include "coeq1d.mm"
include "ccrg.mm"
include "csubrg.mm"
include "cress.mm"
include "cmpl.mm"
include "cbs.mm"
include "wceq.mm"
include "cpl1.mm"
include "cps1.mm"
include "fveq2i.mm"
include "ply1bas.mm"
include "eqcomi.mm"
include "subrgvr1cl.mm"
include "evls1val.mm"
include "syl3anc.mm"
include "crg.mm"
include "crngring.mm"
include "vr1cl.mm"
include "3syl.mm"
include "evl1val.mm"
include "syl2anc.mm"
include "evl1var.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem evls1var
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cX: class X
  let vy: setvar y
  assume evls1var.q: |- Q = ( S evalSub1 R )
  assume evls1var.x: |- X = ( var1 ` U )
  assume evls1var.u: |- U = ( S |`s R )
  assume evls1var.b: |- B = ( Base ` S )
  assume evls1var.s: |- ( ph -> S e. CRing )
  assume evls1var.r: |- ( ph -> R e. ( SubRing ` S ) )


  assert |- ( ph -> ( Q ` X ) = ( _I |` B ) )

  proof
    wph
    cX
    cQ
    cfv
    cS
    cv1
    cfv
    #
    cQ
    cfv
    #
    @0
    cS
    ce1
    cfv
    #
    cfv
    #
    cid
    cB
    cres
    #
    wph
    cX
    @0
    cQ
    wph
    @0
    cU
    cv1
    cfv
    cX
    wph
    cS
    cR
    cU
    @0
    @0
    eqid
    #
    evls1var.r
    evls1var.u
    subrgvr1
    evls1var.x
    syl6reqr
    fveq2d
    wph
    @0
    cR
    c1o
    cS
    ces
    co
    #
    cfv
    #
    cfv
    #
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    @0
    c1o
    cS
    cevl
    co
    #
    cfv
    #
    @9
    ccom
    #
    @1
    @3
    wph
    @8
    @12
    @9
    wph
    c0
    c1o
    cU
    cmvr
    co
    #
    cfv
    #
    @7
    cfv
    @15
    @11
    cfv
    @8
    @12
    wph
    con0
    cB
    @7
    cR
    cS
    cU
    c1o
    @11
    @14
    c0
    @7
    eqid
    @11
    eqid
    #
    @14
    eqid
    evls1var.u
    evls1var.b
    c1o
    con0
    wcel
    wph
    1on
    a1i
    #
    evls1var.s
    evls1var.r
    c0
    c1o
    wcel
    wph
    0lt1o
    a1i
    evlsvarsrng
    wph
    @0
    @15
    @7
    wph
    @0
    c0
    c1o
    cS
    cmvr
    co
    #
    cfv
    @15
    cS
    @0
    @5
    vr1val
    wph
    c0
    @18
    @14
    wph
    cS
    cR
    cU
    c1o
    @18
    con0
    @18
    eqid
    @17
    evls1var.r
    evls1var.u
    subrgmvr
    fveq1d
    syl5eq
    #
    fveq2d
    wph
    @0
    @15
    @11
    @19
    fveq2d
    3eqtr4d
    coeq1d
    wph
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    @0
    c1o
    cS
    cR
    cress
    co
    #
    cmpl
    co
    #
    cbs
    cfv
    #
    wcel
    @1
    @10
    wceq
    evls1var.s
    evls1var.r
    wph
    @23
    cS
    cR
    cU
    cpl1
    cfv
    #
    cU
    @0
    @5
    evls1var.r
    evls1var.u
    @24
    eqid
    @24
    cbs
    cfv
    #
    @23
    @21
    cpl1
    cfv
    #
    @21
    @21
    cps1
    cfv
    #
    @25
    @26
    eqid
    @27
    eqid
    @24
    @26
    cbs
    cU
    @21
    cpl1
    evls1var.u
    fveq2i
    fveq2i
    ply1bas
    eqcomi
    subrgvr1cl
    vy
    @0
    cB
    cQ
    cR
    cS
    @6
    @23
    @22
    evls1var.q
    @6
    eqid
    evls1var.b
    @22
    eqid
    @23
    eqid
    evls1val
    syl3anc
    wph
    @20
    @0
    c1o
    cS
    cmpl
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @13
    wceq
    evls1var.s
    wph
    @20
    cS
    crg
    wcel
    @30
    evls1var.s
    cS
    crngring
    @29
    cS
    cpl1
    cfv
    #
    cS
    @0
    @5
    @31
    eqid
    #
    @31
    cbs
    cfv
    #
    @29
    @31
    cS
    cS
    cps1
    cfv
    #
    @33
    @32
    @34
    eqid
    @33
    eqid
    ply1bas
    eqcomi
    vr1cl
    3syl
    vy
    @0
    cB
    @11
    cS
    @29
    @28
    @2
    @2
    eqid
    #
    @16
    evls1var.b
    @28
    eqid
    @29
    eqid
    evl1val
    syl2anc
    3eqtr4d
    wph
    @20
    @3
    @4
    wceq
    evls1var.s
    cB
    cS
    @2
    @0
    @35
    @5
    evls1var.b
    evl1var
    syl
    3eqtrd
end
