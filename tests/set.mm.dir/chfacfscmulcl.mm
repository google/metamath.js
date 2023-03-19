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
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "crg.mm"
include "crngring.mm"
include "pmatlmod.mm"
include "sylan2.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "ringmgp.mm"
include "simp3.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "wceq.mm"
include "ply1crng.mm"
include "anim2i.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wf.mm"
include "chfacfisf.mm"
include "syl3anl2.mm"
include "ffvelrnd.mm"
include "lmodvscl.mm"

theorem chfacfscmulcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chfacfscmulcl.x: |- X = ( var1 ` R )
  assume chfacfscmulcl.m: |- .x. = ( .s ` Y )
  assume chfacfscmulcl.e: |- .^ = ( .g ` ( mulGrp ` P ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint B k
  disjoint B l
  disjoint k l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint T k
  disjoint T l
  disjoint Y k
  disjoint Y l
  disjoint b k
  disjoint b l
  disjoint k n
  disjoint k s
  disjoint l n
  disjoint l s
  disjoint .X. k
  disjoint .X. l
  disjoint .0. k
  disjoint .0. l
  disjoint .- k
  disjoint .- l
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) /\ K e. NN0 ) -> ( ( K .^ X ) .x. ( G ` K ) ) e. ( Base ` Y ) )

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
    clmod
    wcel
    #
    cK
    cX
    c.ex
    co
    #
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cK
    cG
    cfv
    #
    cY
    cbs
    cfv
    #
    wcel
    @9
    @12
    c.x
    co
    @13
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
    chfacfisf.p
    chfacfisf.y
    pmatlmod
    sylan2
    3adant3
    3ad2ant1
    @7
    @9
    cP
    cbs
    cfv
    #
    @11
    @7
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @6
    cX
    @16
    wcel
    #
    @9
    @16
    wcel
    @3
    @5
    @18
    @6
    @3
    cP
    crg
    wcel
    #
    @18
    @1
    @0
    @20
    @2
    @1
    @14
    @20
    @15
    cP
    cR
    chfacfisf.p
    ply1ring
    syl
    3ad2ant2
    cP
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
    @3
    @14
    @19
    @1
    @0
    @14
    @2
    @15
    3ad2ant2
    @16
    cP
    cR
    cX
    chfacfscmulcl.x
    chfacfisf.p
    @16
    eqid
    #
    vr1cl
    syl
    3ad2ant1
    @16
    c.ex
    @17
    cK
    cX
    @16
    cP
    @17
    @21
    @23
    mgpbas
    chfacfscmulcl.e
    mulgnn0cl
    syl3anc
    @3
    @5
    @11
    @16
    wceq
    @6
    @3
    @10
    cP
    cbs
    @3
    cP
    @10
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    cP
    @10
    wceq
    @0
    @1
    @25
    @2
    @1
    @24
    @0
    cP
    cR
    chfacfisf.p
    ply1crng
    anim2i
    3adant3
    cY
    cP
    cN
    ccrg
    chfacfisf.y
    matsca2
    syl
    eqcomd
    fveq2d
    3ad2ant1
    eleqtrrd
    @7
    cn0
    @13
    cK
    cG
    @3
    @5
    cn0
    @13
    cG
    wf
    #
    @6
    @1
    @0
    @14
    @2
    @5
    @26
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
    chfacfisf.a
    chfacfisf.b
    chfacfisf.p
    chfacfisf.y
    chfacfisf.r
    chfacfisf.s
    chfacfisf.0
    chfacfisf.t
    chfacfisf.g
    chfacfisf
    syl3anl2
    3adant3
    @22
    ffvelrnd
    @9
    c.x
    @10
    @11
    @13
    cY
    @12
    @13
    eqid
    @10
    eqid
    chfacfscmulcl.m
    @11
    eqid
    lmodvscl
    syl3anc
end
