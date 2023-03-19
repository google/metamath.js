include "cchp.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cvma.mm"
include "csu.mm"
include "cc0.mm"
include "c3.mm"
include "c8.mm"
include "cdp2.mm"
include "cdp.mm"
include "cmul.mm"
include "clt.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "nnzd.mm"
include "chpvalz.mm"
include "syl.mm"
include "wbr.mm"
include "crp.mm"
include "fveq2.mm"
include "oveq2.mm"
include "breq12d.mm"
include "wral.mm"
include "ax-ros335.mm"
include "a1i.mm"
include "nnrpd.mm"
include "rspcdva.mm"
include "eqbrtrrd.mm"

theorem hgt750lemc
  let wph: wff ph
  let vj: setvar j
  let cN: class N
  let vi: setvar i
  let vx: setvar x
  assume hgt750lemc.n: |- ( ph -> N e. NN )

  disjoint N j
  disjoint N i
  disjoint i j
  disjoint N x
  disjoint i ph
  disjoint ph x
  disjoint i x
  assert |- ( ph -> sum_ j e. ( 1 ... N ) ( Lam ` j ) < ( ( 1 . _ 0 _ 3 _ 8 _ 8 3 ) x. N ) )

  proof
    wph
    cN
    cchp
    cfv
    #
    c1
    cN
    cfz
    co
    vj
    cv
    cvma
    cfv
    vj
    csu
    #
    c1
    cc0
    c3
    c8
    c8
    c3
    cdp2
    cdp2
    cdp2
    cdp2
    cdp
    co
    #
    cN
    cmul
    co
    #
    clt
    wph
    cN
    cz
    wcel
    @0
    @1
    wceq
    wph
    cN
    hgt750lemc.n
    nnzd
    vj
    cN
    chpvalz
    syl
    wph
    vx
    cv
    #
    cchp
    cfv
    #
    @2
    @4
    cmul
    co
    #
    clt
    wbr
    #
    @0
    @3
    clt
    wbr
    vx
    crp
    cN
    @4
    cN
    wceq
    @5
    @0
    @6
    @3
    clt
    @4
    cN
    cchp
    fveq2
    @4
    cN
    @2
    cmul
    oveq2
    breq12d
    @7
    vx
    crp
    wral
    wph
    vx
    ax-ros335
    a1i
    wph
    cN
    hgt750lemc.n
    nnrpd
    rspcdva
    eqbrtrrd
end
