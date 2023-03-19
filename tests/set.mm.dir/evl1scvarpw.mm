include "co.mm"
include "cfv.mm"
include "cascl.mm"
include "cmulr.mm"
include "csn.mm"
include "cxp.mm"
include "casa.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "ccrg.mm"
include "ply1assa.mm"
include "syl.mm"
include "syl6eleq.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "cmnd.mm"
include "cn0.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "eqid.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "asclmul1.mm"
include "crh.mm"
include "evl1rhm.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "ffvelrnd.mm"
include "rhmmul.mm"
include "evl1sca.mm"
include "syl2anc.mm"
include "cpws.mm"
include "cmgp.mm"
include "cmg.mm"
include "evl1varpw.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "a1i.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem evl1scvarpw
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.xp: class .X.
  let c.ex: class .^
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume evl1varpw.q: |- Q = ( eval1 ` R )
  assume evl1varpw.w: |- W = ( Poly1 ` R )
  assume evl1varpw.g: |- G = ( mulGrp ` W )
  assume evl1varpw.x: |- X = ( var1 ` R )
  assume evl1varpw.b: |- B = ( Base ` R )
  assume evl1varpw.e: |- .^ = ( .g ` G )
  assume evl1varpw.r: |- ( ph -> R e. CRing )
  assume evl1varpw.n: |- ( ph -> N e. NN0 )
  assume evl1scvarpw.t1: |- .X. = ( .s ` W )
  assume evl1scvarpw.a: |- ( ph -> A e. B )
  assume evl1scvarpw.s: |- S = ( R ^s B )
  assume evl1scvarpw.t2: |- .xb = ( .r ` S )
  assume evl1scvarpw.m: |- M = ( mulGrp ` S )
  assume evl1scvarpw.f: |- F = ( .g ` M )


  assert |- ( ph -> ( Q ` ( A .X. ( N .^ X ) ) ) = ( ( B X. { A } ) .xb ( N F ( Q ` X ) ) ) )

  proof
    wph
    cA
    cN
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    cQ
    cfv
    cA
    cW
    cascl
    cfv
    #
    cfv
    #
    @0
    cW
    cmulr
    cfv
    #
    co
    #
    cQ
    cfv
    #
    @3
    cQ
    cfv
    #
    @0
    cQ
    cfv
    #
    c.xb
    co
    #
    cB
    cA
    csn
    cxp
    #
    cN
    cX
    cQ
    cfv
    #
    cF
    co
    #
    c.xb
    co
    wph
    @1
    @5
    cQ
    wph
    @5
    @1
    wph
    cW
    casa
    wcel
    #
    cA
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @0
    cW
    cbs
    cfv
    #
    wcel
    #
    @5
    @1
    wceq
    wph
    cR
    ccrg
    wcel
    #
    @13
    evl1varpw.r
    cW
    cR
    evl1varpw.w
    ply1assa
    syl
    wph
    cA
    cR
    cbs
    cfv
    #
    @15
    wph
    cA
    cB
    @19
    evl1scvarpw.a
    evl1varpw.b
    syl6eleq
    wph
    @14
    cR
    cbs
    wph
    @18
    @14
    cR
    wceq
    evl1varpw.r
    @18
    cR
    @14
    cW
    cR
    ccrg
    evl1varpw.w
    ply1sca
    eqcomd
    syl
    fveq2d
    eleqtrrd
    #
    wph
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    cX
    @16
    wcel
    #
    @17
    wph
    cW
    crg
    wcel
    #
    @21
    wph
    cR
    crg
    wcel
    #
    @23
    wph
    @18
    @24
    evl1varpw.r
    cR
    crngring
    syl
    #
    cW
    cR
    evl1varpw.w
    ply1ring
    syl
    #
    cW
    cG
    evl1varpw.g
    ringmgp
    syl
    evl1varpw.n
    wph
    @24
    @22
    @25
    @16
    cW
    cR
    cX
    evl1varpw.x
    evl1varpw.w
    @16
    eqid
    #
    vr1cl
    syl
    @16
    c.ex
    cG
    cN
    cX
    @16
    cW
    cG
    evl1varpw.g
    @27
    mgpbas
    evl1varpw.e
    mulgnn0cl
    syl3anc
    #
    @2
    cA
    c.xp
    @4
    @14
    @15
    @16
    cW
    @0
    @2
    eqid
    #
    @14
    eqid
    #
    @15
    eqid
    #
    @27
    @4
    eqid
    #
    evl1scvarpw.t1
    asclmul1
    syl3anc
    eqcomd
    fveq2d
    wph
    cQ
    cW
    cS
    crh
    co
    wcel
    #
    @3
    @16
    wcel
    @17
    @6
    @9
    wceq
    wph
    @18
    @33
    evl1varpw.r
    cB
    cW
    cR
    cS
    cQ
    evl1varpw.q
    evl1varpw.w
    evl1scvarpw.s
    evl1varpw.b
    evl1rhm
    syl
    wph
    @15
    @16
    cA
    @2
    wph
    @2
    @16
    @14
    @15
    cW
    @29
    @30
    @26
    wph
    @24
    cW
    clmod
    wcel
    @25
    cW
    cR
    evl1varpw.w
    ply1lmod
    syl
    @31
    @27
    asclf
    @20
    ffvelrnd
    @28
    @3
    @0
    cW
    cS
    @4
    c.xb
    cQ
    @16
    @27
    @32
    evl1scvarpw.t2
    rhmmul
    syl3anc
    wph
    @7
    @10
    @8
    @12
    c.xb
    wph
    @18
    cA
    cB
    wcel
    @7
    @10
    wceq
    evl1varpw.r
    evl1scvarpw.a
    @2
    cB
    cW
    cR
    cQ
    cA
    evl1varpw.q
    evl1varpw.w
    evl1varpw.b
    @29
    evl1sca
    syl2anc
    wph
    @8
    cN
    @11
    cR
    cB
    cpws
    co
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    @12
    wph
    cB
    cQ
    cR
    c.ex
    cG
    cN
    cW
    cX
    evl1varpw.q
    evl1varpw.w
    evl1varpw.g
    evl1varpw.x
    evl1varpw.b
    evl1varpw.e
    evl1varpw.r
    evl1varpw.n
    evl1varpw
    wph
    @36
    cF
    cN
    @11
    wph
    cF
    @36
    cF
    @36
    wceq
    wph
    cF
    cM
    cmg
    cfv
    @36
    evl1scvarpw.f
    cM
    @35
    cmg
    cM
    cS
    cmgp
    cfv
    @35
    evl1scvarpw.m
    cS
    @34
    cmgp
    evl1scvarpw.s
    fveq2i
    eqtri
    fveq2i
    eqtri
    a1i
    eqcomd
    oveqd
    eqtrd
    oveq12d
    3eqtrd
end
