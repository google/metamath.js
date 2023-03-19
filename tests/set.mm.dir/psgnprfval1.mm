include "c1.mm"
include "cop.mm"
include "c2.mm"
include "cpr.mm"
include "cfv.mm"
include "c0.mm"
include "cgsu.mm"
include "co.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "wcel.mm"
include "c0g.mm"
include "wceq.mm"
include "prex.mm"
include "eqeltri.mm"
include "symgid.mm"
include "ax-mp.mm"
include "gsum0.mm"
include "reseq2.mm"
include "cn.mm"
include "1ex.mm"
include "2nn.mm"
include "residpr.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "eqtr2i.mm"
include "fveq2i.mm"
include "cword.mm"
include "wrd0.mm"
include "psgnvalii.mm"
include "cc0.mm"
include "hash0.mm"
include "oveq2i.mm"
include "cc.mm"
include "neg1cn.mm"
include "exp0.mm"
include "eqtri.mm"
include "3eqtri.mm"

theorem psgnprfval1
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vw: setvar w
  let cX: class X
  assume psgnprfval.0: |- D = { 1 , 2 }
  assume psgnprfval.g: |- G = ( SymGrp ` D )
  assume psgnprfval.b: |- B = ( Base ` G )
  assume psgnprfval.t: |- T = ran ( pmTrsp ` D )
  assume psgnprfval.n: |- N = ( pmSgn ` D )


  assert |- ( N ` { <. 1 , 1 >. , <. 2 , 2 >. } ) = 1

  proof
    c1
    c1
    cop
    c2
    c2
    cop
    cpr
    #
    cN
    cfv
    cG
    c0
    cgsu
    co
    #
    cN
    cfv
    #
    c1
    cneg
    #
    c0
    chash
    cfv
    #
    cexp
    co
    #
    c1
    @0
    @1
    cN
    @1
    cid
    cD
    cres
    #
    @0
    cG
    @6
    cD
    cvv
    wcel
    #
    @6
    cG
    c0g
    cfv
    wceq
    cD
    c1
    c2
    cpr
    #
    cvv
    psgnprfval.0
    c1
    c2
    prex
    eqeltri
    #
    cD
    cG
    cvv
    psgnprfval.g
    symgid
    ax-mp
    gsum0
    cD
    @8
    wceq
    #
    @6
    @0
    wceq
    psgnprfval.0
    @10
    @6
    cid
    @8
    cres
    #
    @0
    cD
    @8
    cid
    reseq2
    c1
    cvv
    wcel
    c2
    cn
    wcel
    @11
    @0
    wceq
    1ex
    2nn
    c1
    c2
    cvv
    cn
    residpr
    mp2an
    syl6eq
    ax-mp
    eqtr2i
    fveq2i
    @7
    c0
    cT
    cword
    wcel
    @2
    @5
    wceq
    @9
    cT
    wrd0
    cD
    cT
    cG
    cN
    cvv
    c0
    psgnprfval.g
    psgnprfval.t
    psgnprfval.n
    psgnvalii
    mp2an
    @5
    @3
    cc0
    cexp
    co
    #
    c1
    @4
    cc0
    @3
    cexp
    hash0
    oveq2i
    @3
    cc
    wcel
    @12
    c1
    wceq
    neg1cn
    @3
    exp0
    ax-mp
    eqtri
    3eqtri
end
