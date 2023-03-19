include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cn0.mm"
include "crg.mm"
include "cfv.mm"
include "cbs.mm"
include "crngring.mm"
include "pmatring.mm"
include "sylan2.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "cmgp.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "syl.mm"
include "simp3.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "wf.mm"
include "chfacfisf.mm"
include "syl3anl2.mm"
include "ffvelrnd.mm"
include "ringcl.mm"

theorem chfacfpmmulcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  assume cayhamlem1.a: |- A = ( N Mat R )
  assume cayhamlem1.b: |- B = ( Base ` A )
  assume cayhamlem1.p: |- P = ( Poly1 ` R )
  assume cayhamlem1.y: |- Y = ( N Mat P )
  assume cayhamlem1.r: |- .X. = ( .r ` Y )
  assume cayhamlem1.s: |- .- = ( -g ` Y )
  assume cayhamlem1.0: |- .0. = ( 0g ` Y )
  assume cayhamlem1.t: |- T = ( N matToPolyMat R )
  assume cayhamlem1.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cayhamlem1.e: |- .^ = ( .g ` ( mulGrp ` Y ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) /\ K e. NN0 ) -> ( ( K .^ ( T ` M ) ) .X. ( G ` K ) ) e. ( Base ` Y ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn
    wcel
    vb
    cv
    cB
    cc0
    @4
    cfz
    co
    cmap
    co
    wcel
    wa
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    cY
    crg
    wcel
    #
    cK
    cM
    cT
    cfv
    #
    c.ex
    co
    #
    cY
    cbs
    cfv
    #
    wcel
    #
    cK
    cG
    cfv
    #
    @11
    wcel
    @10
    @13
    c.xp
    co
    @11
    wcel
    @3
    @5
    @8
    @6
    @0
    @1
    @8
    @2
    @1
    @0
    cR
    crg
    wcel
    #
    @8
    cR
    crngring
    #
    cY
    cP
    cR
    cN
    cayhamlem1.p
    cayhamlem1.y
    pmatring
    sylan2
    3adant3
    #
    3ad2ant1
    @7
    cY
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @6
    @9
    @11
    wcel
    #
    @12
    @3
    @5
    @18
    @6
    @3
    @8
    @18
    @16
    cY
    @17
    @17
    eqid
    #
    ringmgp
    syl
    3ad2ant1
    @3
    @5
    @6
    simp3
    #
    @3
    @5
    @19
    @6
    @1
    @0
    @14
    @2
    @19
    @15
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3an2
    3ad2ant1
    @11
    c.ex
    @17
    cK
    @9
    @11
    cY
    @17
    @20
    @11
    eqid
    #
    mgpbas
    cayhamlem1.e
    mulgnn0cl
    syl3anc
    @7
    cn0
    @11
    cK
    cG
    @3
    @5
    cn0
    @11
    cG
    wf
    #
    @6
    @1
    @0
    @14
    @2
    @5
    @23
    @15
    cA
    cB
    cP
    cR
    cT
    c.xp
    vn
    cG
    cM
    c.mi
    cN
    cY
    c.0
    vs
    vb
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    cayhamlem1.r
    cayhamlem1.s
    cayhamlem1.0
    cayhamlem1.t
    cayhamlem1.g
    chfacfisf
    syl3anl2
    3adant3
    @21
    ffvelrnd
    @11
    cY
    c.xp
    @10
    @13
    @22
    cayhamlem1.r
    ringcl
    syl3anc
end
