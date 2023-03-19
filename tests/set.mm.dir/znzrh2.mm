include "cn0.mm"
include "wcel.mm"
include "czrh.mm"
include "cfv.mm"
include "cz.mm"
include "cv.mm"
include "cec.mm"
include "cmpt.mm"
include "zring.mm"
include "cqus.mm"
include "co.mm"
include "crh.mm"
include "wceq.mm"
include "crg.mm"
include "csn.mm"
include "clidl.mm"
include "zringring.mm"
include "nn0z.mm"
include "znlidl.mm"
include "syl.mm"
include "cqg.mm"
include "oveq2i.mm"
include "ccrg.mm"
include "c2idl.mm"
include "zringcrng.mm"
include "eqid.mm"
include "crng2idl.mm"
include "ax-mp.mm"
include "zringbas.mm"
include "eceq2.mm"
include "mpteq2i.mm"
include "qusrhm.mm"
include "sylancr.mm"
include "wb.mm"
include "zncrng2.mm"
include "crngring.mm"
include "zrhrhmb.mm"
include "4syl.mm"
include "mpbid.mm"
include "znzrh.mm"
include "eqtr2d.mm"
include "syl5eq.mm"

theorem znzrh2
  let vx: setvar x
  let c.sm: class .~
  let cS: class S
  let cL: class L
  let cN: class N
  let cY: class Y
  let cA: class A
  assume znzrh2.s: |- S = ( RSpan ` ZZring )
  assume znzrh2.r: |- .~ = ( ZZring ~QG ( S ` { N } ) )
  assume znzrh2.y: |- Y = ( Z/nZ ` N )
  assume znzrh2.2: |- L = ( ZRHom ` Y )

  disjoint N x
  disjoint .~ x
  disjoint S x
  disjoint A x
  assert |- ( N e. NN0 -> L = ( x e. ZZ |-> [ x ] .~ ) )

  proof
    cN
    cn0
    wcel
    #
    cL
    cY
    czrh
    cfv
    #
    vx
    cz
    vx
    cv
    #
    c.sm
    cec
    #
    cmpt
    #
    znzrh2.2
    @0
    @4
    zring
    c.sm
    cqus
    co
    #
    czrh
    cfv
    #
    @1
    @0
    @4
    zring
    @5
    crh
    co
    wcel
    #
    @4
    @6
    wceq
    #
    @0
    zring
    crg
    wcel
    cN
    csn
    cS
    cfv
    #
    zring
    clidl
    cfv
    #
    wcel
    #
    @7
    zringring
    @0
    cN
    cz
    wcel
    #
    @11
    cN
    nn0z
    #
    cS
    cN
    znzrh2.s
    znlidl
    syl
    vx
    zring
    @9
    @5
    @4
    @10
    cz
    c.sm
    zring
    @9
    cqg
    co
    #
    zring
    cqus
    znzrh2.r
    oveq2i
    #
    zring
    ccrg
    wcel
    @10
    zring
    c2idl
    cfv
    wceq
    zringcrng
    zring
    @10
    @10
    eqid
    crng2idl
    ax-mp
    zringbas
    vx
    cz
    @3
    @2
    @14
    cec
    #
    c.sm
    @14
    wceq
    @3
    @16
    wceq
    znzrh2.r
    c.sm
    @14
    @2
    eceq2
    ax-mp
    mpteq2i
    qusrhm
    sylancr
    @0
    @12
    @5
    ccrg
    wcel
    @5
    crg
    wcel
    @7
    @8
    wb
    @13
    cS
    @5
    cN
    znzrh2.s
    @15
    zncrng2
    @5
    crngring
    @5
    @4
    @6
    @6
    eqid
    zrhrhmb
    4syl
    mpbid
    cS
    @5
    cN
    cY
    znzrh2.s
    @15
    znzrh2.y
    znzrh
    eqtr2d
    syl5eq
end
