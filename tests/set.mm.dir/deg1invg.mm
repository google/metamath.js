include "cid.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "crg.mm"
include "ply1lmod.mm"
include "syl.mm"
include "ply1sca2.mm"
include "eqid.mm"
include "grpinvfvi.mm"
include "lmodvneg1.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "crlreg.mm"
include "fvi.mm"
include "cui.mm"
include "wss.mm"
include "unitrrg.mm"
include "1unit.mm"
include "unitnegcl.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "deg1vsca.mm"
include "eqtr3d.mm"

theorem deg1invg
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cF: class F
  let cN: class N
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1invg.b: |- B = ( Base ` Y )
  assume deg1invg.n: |- N = ( invg ` Y )
  assume deg1invg.f: |- ( ph -> F e. B )


  assert |- ( ph -> ( D ` ( N ` F ) ) = ( D ` F ) )

  proof
    wph
    cR
    cid
    cfv
    #
    cur
    cfv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    cF
    cY
    cvsca
    cfv
    #
    co
    #
    cD
    cfv
    cF
    cN
    cfv
    #
    cD
    cfv
    cF
    cD
    cfv
    wph
    @5
    @6
    cD
    wph
    cY
    clmod
    wcel
    #
    cF
    cB
    wcel
    @5
    @6
    wceq
    wph
    cR
    crg
    wcel
    #
    @7
    deg1addle.r
    cY
    cR
    deg1addle.y
    ply1lmod
    syl
    deg1invg.f
    @4
    @1
    @0
    @2
    cN
    cB
    cY
    cF
    deg1invg.b
    deg1invg.n
    cY
    cR
    deg1addle.y
    ply1sca2
    @4
    eqid
    #
    @1
    eqid
    cR
    @2
    @2
    eqid
    #
    grpinvfvi
    lmodvneg1
    syl2anc
    fveq2d
    wph
    cB
    cD
    cR
    @4
    cR
    crlreg
    cfv
    #
    @3
    cF
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1invg.b
    @11
    eqid
    #
    @9
    wph
    @3
    cR
    cur
    cfv
    #
    @2
    cfv
    #
    @11
    wph
    @1
    @13
    @2
    wph
    @0
    cR
    cur
    wph
    @8
    @0
    cR
    wceq
    deg1addle.r
    cR
    crg
    fvi
    syl
    fveq2d
    fveq2d
    wph
    cR
    cui
    cfv
    #
    @11
    @14
    wph
    @8
    @15
    @11
    wss
    deg1addle.r
    cR
    @15
    @11
    @12
    @15
    eqid
    #
    unitrrg
    syl
    wph
    @8
    @13
    @15
    wcel
    #
    @14
    @15
    wcel
    deg1addle.r
    wph
    @8
    @17
    deg1addle.r
    cR
    @15
    @13
    @16
    @13
    eqid
    1unit
    syl
    cR
    @15
    @2
    @13
    @16
    @10
    unitnegcl
    syl2anc
    sseldd
    eqeltrd
    deg1invg.f
    deg1vsca
    eqtr3d
end
