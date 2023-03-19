include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "nn0nndivcl.mm"
include "nn0ge0div.mm"
include "flge0nn0.mm"
include "syl2anc.mm"

theorem fldivnn0
  let cK: class K
  let cL: class L


  assert |- ( ( K e. NN0 /\ L e. NN ) -> ( |_ ` ( K / L ) ) e. NN0 )

  proof
    cK
    cn0
    wcel
    cL
    cn
    wcel
    wa
    cK
    cL
    cdiv
    co
    #
    cr
    wcel
    cc0
    @0
    cle
    wbr
    @0
    cfl
    cfv
    cn0
    wcel
    cK
    cL
    nn0nndivcl
    cK
    cL
    nn0ge0div
    @0
    flge0nn0
    syl2anc
end
