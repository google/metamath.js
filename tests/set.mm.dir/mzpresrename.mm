include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cmzp.mm"
include "cfv.mm"
include "w3a.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "cid.mm"
include "ccom.mm"
include "coires1.mm"
include "fveq2i.mm"
include "mpteq2i.mm"
include "wf.mm"
include "simp1.mm"
include "simp3.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "fss.mm"
include "mpan.mm"
include "3ad2ant2.mm"
include "mzprename.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem mzpresrename
  let vx: setvar x
  let cF: class F
  let cV: class V
  let cW: class W

  disjoint W x
  disjoint F x
  disjoint V x
  assert |- ( ( W e. _V /\ V C_ W /\ F e. ( mzPoly ` V ) ) -> ( x e. ( ZZ ^m W ) |-> ( F ` ( x |` V ) ) ) e. ( mzPoly ` W ) )

  proof
    cW
    cvv
    wcel
    #
    cV
    cW
    wss
    #
    cF
    cV
    cmzp
    cfv
    wcel
    #
    w3a
    #
    vx
    cz
    cW
    cmap
    co
    #
    vx
    cv
    #
    cV
    cres
    #
    cF
    cfv
    #
    cmpt
    vx
    @4
    @5
    cid
    cV
    cres
    #
    ccom
    #
    cF
    cfv
    #
    cmpt
    #
    cW
    cmzp
    cfv
    #
    vx
    @4
    @10
    @7
    @9
    @6
    cF
    @5
    cV
    coires1
    fveq2i
    mpteq2i
    @3
    @0
    @2
    cV
    cW
    @8
    wf
    #
    @11
    @12
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @1
    @0
    @13
    @2
    cV
    cV
    @8
    wf
    #
    @1
    @13
    cV
    cV
    @8
    wf1o
    @14
    cV
    f1oi
    cV
    cV
    @8
    f1of
    ax-mp
    cV
    cV
    cW
    @8
    fss
    mpan
    3ad2ant2
    vx
    @8
    cF
    cV
    cW
    mzprename
    syl3anc
    syl5eqelr
end
