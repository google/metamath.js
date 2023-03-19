include "wcel.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "fveq1i.mm"
include "cvv.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wceq.mm"
include "s1cli.mm"
include "cuz.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "nn0uz.mm"
include "eleqtri.mm"
include "lencl.mm"
include "nn0z.mm"
include "mp2b.mm"
include "breqtrri.mm"
include "elfzo2.mm"
include "mpbir3an.mm"
include "ccatval1.mm"
include "mp3an.mm"
include "eqtri.mm"
include "syl5eq.mm"

theorem cats1fv
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cli.2: |- S e. Word _V
  assume cats1fvn.3: |- ( # ` S ) = M
  assume cats1fv.4: |- ( Y e. V -> ( S ` N ) = Y )
  assume cats1fv.5: |- N e. NN0
  assume cats1fv.6: |- N < M


  assert |- ( Y e. V -> ( T ` N ) = Y )

  proof
    cY
    cV
    wcel
    cN
    cT
    cfv
    #
    cN
    cS
    cfv
    #
    cY
    @0
    cN
    cS
    cX
    cs1
    #
    cconcat
    co
    #
    cfv
    #
    @1
    cN
    cT
    @3
    cats1cld.1
    fveq1i
    cS
    cvv
    cword
    #
    wcel
    #
    @2
    @5
    wcel
    cN
    cc0
    cS
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    @4
    @1
    wceq
    cats1cli.2
    cX
    s1cli
    @8
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    #
    cN
    @7
    clt
    wbr
    cN
    cn0
    @9
    cats1fv.5
    nn0uz
    eleqtri
    @6
    @7
    cn0
    wcel
    @10
    cats1cli.2
    cvv
    cS
    lencl
    @7
    nn0z
    mp2b
    cN
    cM
    @7
    clt
    cats1fv.6
    cats1fvn.3
    breqtrri
    cN
    cc0
    @7
    elfzo2
    mpbir3an
    cvv
    cS
    @2
    cN
    ccatval1
    mp3an
    eqtri
    cats1fv.4
    syl5eq
end
