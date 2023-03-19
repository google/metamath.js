include "co.mm"
include "cfv.mm"
include "cress.mm"
include "cv1.mm"
include "cpl1.mm"
include "cmgp.mm"
include "cmg.mm"
include "ces1.mm"
include "cpws.mm"
include "wceq.mm"
include "evl1fval1.mm"
include "a1i.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "ccrg.mm"
include "wcel.mm"
include "ressid.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "fveq12d.mm"
include "eqid.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "evls1varpw.mm"
include "eqcomi.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem evl1varpw
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.ex: class .^
  let cG: class G
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


  assert |- ( ph -> ( Q ` ( N .^ X ) ) = ( N ( .g ` ( mulGrp ` ( R ^s B ) ) ) ( Q ` X ) ) )

  proof
    wph
    cN
    cX
    c.ex
    co
    #
    cQ
    cfv
    cN
    cR
    cB
    cress
    co
    #
    cv1
    cfv
    #
    @1
    cpl1
    cfv
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cR
    cB
    ces1
    co
    #
    cfv
    cN
    @2
    @7
    cfv
    #
    cR
    cB
    cpws
    co
    cmgp
    cfv
    cmg
    cfv
    #
    co
    cN
    cX
    cQ
    cfv
    #
    @9
    co
    wph
    @0
    @6
    cQ
    @7
    cQ
    @7
    wceq
    wph
    cB
    cQ
    cR
    evl1varpw.q
    evl1varpw.b
    evl1fval1
    #
    a1i
    wph
    cN
    cN
    cX
    @2
    c.ex
    @5
    wph
    c.ex
    cR
    cpl1
    cfv
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    @5
    c.ex
    cG
    cmg
    cfv
    @14
    evl1varpw.e
    cG
    @13
    cmg
    cG
    cW
    cmgp
    cfv
    @13
    evl1varpw.g
    cW
    @12
    cmgp
    evl1varpw.w
    fveq2i
    eqtri
    fveq2i
    eqtri
    wph
    @13
    @4
    cmg
    wph
    @12
    @3
    cmgp
    wph
    cR
    @1
    cpl1
    wph
    @1
    cR
    wph
    cR
    ccrg
    wcel
    #
    @1
    cR
    wceq
    evl1varpw.r
    cB
    cR
    ccrg
    evl1varpw.b
    ressid
    syl
    eqcomd
    #
    fveq2d
    fveq2d
    fveq2d
    syl5eq
    wph
    cN
    eqidd
    wph
    cX
    cR
    cv1
    cfv
    @2
    evl1varpw.x
    wph
    cR
    @1
    cv1
    @16
    fveq2d
    syl5eq
    #
    oveq123d
    fveq12d
    wph
    cB
    @7
    cB
    cR
    @1
    @5
    @4
    cN
    @3
    @2
    @7
    eqid
    @1
    eqid
    @3
    eqid
    @4
    eqid
    @2
    eqid
    evl1varpw.b
    @5
    eqid
    evl1varpw.r
    wph
    @15
    cR
    crg
    wcel
    cB
    cR
    csubrg
    cfv
    wcel
    evl1varpw.r
    cR
    crngring
    cB
    cR
    evl1varpw.b
    subrgid
    3syl
    evl1varpw.n
    evls1varpw
    wph
    @8
    @10
    cN
    @9
    wph
    @2
    cX
    @7
    cQ
    @7
    cQ
    wceq
    wph
    cQ
    @7
    @11
    eqcomi
    a1i
    wph
    cX
    @2
    @17
    eqcomd
    fveq12d
    oveq2d
    3eqtrd
end
