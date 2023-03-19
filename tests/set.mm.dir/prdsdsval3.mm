include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cds.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "prdsdsval2.mm"
include "wceq.mm"
include "wral.mm"
include "eqidd.mm"
include "wcel.mm"
include "prdsbascl.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "ex.mm"
include "ral2imi.mm"
include "sylc.mm"
include "mpteq12.mm"
include "syl2anc.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "supeq1d.mm"
include "eqtr4d.mm"

theorem prdsdsval3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume prdsbasmpt2.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbasmpt2.b: |- B = ( Base ` Y )
  assume prdsbasmpt2.s: |- ( ph -> S e. V )
  assume prdsbasmpt2.i: |- ( ph -> I e. W )
  assume prdsbasmpt2.r: |- ( ph -> A. x e. I R e. X )
  assume prdsdsval2.f: |- ( ph -> F e. B )
  assume prdsdsval2.g: |- ( ph -> G e. B )
  assume prdsdsval3.k: |- K = ( Base ` R )
  assume prdsdsval3.e: |- E = ( ( dist ` R ) |` ( K X. K ) )
  assume prdsdsval3.d: |- D = ( dist ` Y )

  disjoint F x
  disjoint G x
  disjoint I x
  disjoint B y
  disjoint x y
  disjoint F y
  disjoint G y
  disjoint ph y
  disjoint S y
  disjoint V y
  disjoint I y
  disjoint R y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |-> ( ( F ` x ) E ( G ` x ) ) ) u. { 0 } ) , RR* , < ) )

  proof
    wph
    cF
    cG
    cD
    co
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cR
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    vx
    cI
    @1
    @2
    cE
    co
    #
    cmpt
    #
    crn
    #
    @7
    cun
    #
    cxr
    clt
    csup
    wph
    vx
    cB
    cD
    cR
    cS
    @3
    cF
    cG
    cI
    cV
    cW
    cX
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    prdsbasmpt2.r
    prdsdsval2.f
    prdsdsval2.g
    @3
    eqid
    prdsdsval3.d
    prdsdsval2
    wph
    cxr
    @12
    @8
    clt
    wph
    @11
    @6
    @7
    wph
    @10
    @5
    wph
    cI
    cI
    wceq
    @9
    @4
    wceq
    #
    vx
    cI
    wral
    #
    @10
    @5
    wceq
    wph
    cI
    eqidd
    wph
    @1
    cK
    wcel
    #
    vx
    cI
    wral
    @2
    cK
    wcel
    #
    vx
    cI
    wral
    @14
    wph
    vx
    cB
    cR
    cS
    cF
    cI
    cK
    cV
    cW
    cX
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    prdsbasmpt2.r
    prdsdsval3.k
    prdsdsval2.f
    prdsbascl
    wph
    vx
    cB
    cR
    cS
    cG
    cI
    cK
    cV
    cW
    cX
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    prdsbasmpt2.r
    prdsdsval3.k
    prdsdsval2.g
    prdsbascl
    @15
    @16
    @13
    vx
    cI
    @15
    @16
    @13
    @15
    @16
    wa
    @9
    @1
    @2
    @3
    cK
    cK
    cxp
    cres
    #
    co
    @4
    cE
    @17
    @1
    @2
    prdsdsval3.e
    oveqi
    @1
    @2
    cK
    cK
    @3
    ovres
    syl5eq
    ex
    ral2imi
    sylc
    vx
    cI
    @9
    cI
    @4
    mpteq12
    syl2anc
    rneqd
    uneq1d
    supeq1d
    eqtr4d
end
