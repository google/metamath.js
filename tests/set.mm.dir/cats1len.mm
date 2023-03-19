include "chash.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "fveq2i.mm"
include "c1.mm"
include "caddc.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "s1cli.mm"
include "ccatlen.mm"
include "mp2an.mm"
include "s1len.mm"
include "oveq12i.mm"
include "eqtri.mm"

theorem cats1len
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cli.2: |- S e. Word _V
  assume cats1fvn.3: |- ( # ` S ) = M
  assume cats1len.4: |- ( M + 1 ) = N


  assert |- ( # ` T ) = N

  proof
    cT
    chash
    cfv
    cS
    cX
    cs1
    #
    cconcat
    co
    #
    chash
    cfv
    #
    cN
    cT
    @1
    chash
    cats1cld.1
    fveq2i
    @2
    cM
    c1
    caddc
    co
    #
    cN
    @2
    cS
    chash
    cfv
    #
    @0
    chash
    cfv
    #
    caddc
    co
    #
    @3
    cS
    cvv
    cword
    #
    wcel
    @0
    @7
    wcel
    @2
    @6
    wceq
    cats1cli.2
    cX
    s1cli
    cvv
    cS
    @0
    ccatlen
    mp2an
    @4
    cM
    @5
    c1
    caddc
    cats1fvn.3
    cX
    s1len
    oveq12i
    eqtri
    cats1len.4
    eqtri
    eqtri
end
