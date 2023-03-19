include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cs1.mm"
include "chash.mm"
include "caddc.mm"
include "co.mm"
include "cconcat.mm"
include "oveq2i.mm"
include "cn0.mm"
include "cvv.mm"
include "cword.mm"
include "lencl.mm"
include "ax-mp.mm"
include "eqeltrri.mm"
include "nn0cni.mm"
include "addid2i.mm"
include "eqtr2i.mm"
include "fveq12i.mm"
include "cfzo.mm"
include "wceq.mm"
include "s1cli.mm"
include "cn.mm"
include "c1.mm"
include "s1len.mm"
include "1nn.mm"
include "eqeltri.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "ccatval3.mm"
include "mp3an.mm"
include "eqtri.mm"
include "s1fv.mm"
include "syl5eq.mm"

theorem cats1fvn
  let cS: class S
  let cT: class T
  let cM: class M
  let cV: class V
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cli.2: |- S e. Word _V
  assume cats1fvn.3: |- ( # ` S ) = M


  assert |- ( X e. V -> ( T ` M ) = X )

  proof
    cX
    cV
    wcel
    cM
    cT
    cfv
    #
    cc0
    cX
    cs1
    #
    cfv
    #
    cX
    @0
    cc0
    cS
    chash
    cfv
    #
    caddc
    co
    #
    cS
    @1
    cconcat
    co
    #
    cfv
    #
    @2
    cM
    @4
    cT
    @5
    cats1cld.1
    @4
    cc0
    cM
    caddc
    co
    cM
    @3
    cM
    cc0
    caddc
    cats1fvn.3
    oveq2i
    cM
    cM
    @3
    cM
    cn0
    cats1fvn.3
    cS
    cvv
    cword
    #
    wcel
    #
    @3
    cn0
    wcel
    cats1cli.2
    cvv
    cS
    lencl
    ax-mp
    eqeltrri
    nn0cni
    addid2i
    eqtr2i
    fveq12i
    @8
    @1
    @7
    wcel
    cc0
    cc0
    @1
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @6
    @2
    wceq
    cats1cli.2
    cX
    s1cli
    @10
    @9
    cn
    wcel
    @9
    c1
    cn
    cX
    s1len
    1nn
    eqeltri
    @9
    lbfzo0
    mpbir
    cvv
    cS
    @1
    cc0
    ccatval3
    mp3an
    eqtri
    cX
    cV
    s1fv
    syl5eq
end
