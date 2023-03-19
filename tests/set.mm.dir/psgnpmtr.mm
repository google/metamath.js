include "wcel.mm"
include "cs1.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "symgtrf.mm"
include "sseli.mm"
include "gsumws1.mm"
include "syl.mm"
include "fveq2d.mm"
include "chash.mm"
include "cexp.mm"
include "cvv.mm"
include "cword.mm"
include "csymg.mm"
include "elbasfv.mm"
include "s1cl.mm"
include "psgnvalii.mm"
include "syl2anc.mm"
include "s1len.mm"
include "oveq2i.mm"
include "cc.mm"
include "neg1cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem psgnpmtr
  let cD: class D
  let cP: class P
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vp: setvar p
  let cV: class V
  let cW: class W
  assume psgnval.g: |- G = ( SymGrp ` D )
  assume psgnval.t: |- T = ran ( pmTrsp ` D )
  assume psgnval.n: |- N = ( pmSgn ` D )


  assert |- ( P e. T -> ( N ` P ) = -u 1 )

  proof
    cP
    cT
    wcel
    #
    cG
    cP
    cs1
    #
    cgsu
    co
    #
    cN
    cfv
    #
    cP
    cN
    cfv
    c1
    cneg
    #
    @0
    @2
    cP
    cN
    @0
    cP
    cG
    cbs
    cfv
    #
    wcel
    #
    @2
    cP
    wceq
    cT
    @5
    cP
    @5
    cD
    cT
    cG
    psgnval.t
    psgnval.g
    @5
    eqid
    #
    symgtrf
    sseli
    #
    @5
    cP
    cG
    @7
    gsumws1
    syl
    fveq2d
    @0
    @3
    @4
    @1
    chash
    cfv
    #
    cexp
    co
    #
    @4
    @0
    cD
    cvv
    wcel
    #
    @1
    cT
    cword
    wcel
    @3
    @10
    wceq
    @0
    @6
    @11
    @8
    @5
    cG
    csymg
    cP
    cD
    psgnval.g
    @7
    elbasfv
    syl
    cP
    cT
    s1cl
    cD
    cT
    cG
    cN
    cvv
    @1
    psgnval.g
    psgnval.t
    psgnval.n
    psgnvalii
    syl2anc
    @10
    @4
    c1
    cexp
    co
    #
    @4
    @9
    c1
    @4
    cexp
    cP
    s1len
    oveq2i
    @4
    cc
    wcel
    @12
    @4
    wceq
    neg1cn
    @4
    exp1
    ax-mp
    eqtri
    syl6eq
    eqtr3d
end
