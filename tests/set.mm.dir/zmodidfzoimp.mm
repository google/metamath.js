include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo0.mm"
include "nn0z.mm"
include "anim1i.mm"
include "3adant3.mm"
include "sylbi.mm"
include "zmodidfzo.mm"
include "biimprd.mm"
include "mpcom.mm"

theorem zmodidfzoimp
  let cM: class M
  let cN: class N


  assert |- ( M e. ( 0 ..^ N ) -> ( M mod N ) = M )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cc0
    cN
    cfzo
    co
    wcel
    #
    cM
    cN
    cmo
    co
    cM
    wceq
    #
    @3
    cM
    cn0
    wcel
    #
    @1
    cM
    cN
    clt
    wbr
    #
    w3a
    @2
    cM
    cN
    elfzo0
    @5
    @1
    @2
    @6
    @5
    @0
    @1
    cM
    nn0z
    anim1i
    3adant3
    sylbi
    @2
    @4
    @3
    cM
    cN
    zmodidfzo
    biimprd
    mpcom
end
