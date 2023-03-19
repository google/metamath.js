include "wcel.mm"
include "wwe.mm"
include "wa.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cep.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "copab.mm"
include "wor.mm"
include "cpw.mm"
include "word.mm"
include "com.mm"
include "2onn.mm"
include "nnord.mm"
include "ax-mp.mm"
include "ordwe.mm"
include "weso.mm"
include "mp2b.mm"
include "eqid.mm"
include "wemapso.mm"
include "mp3an3.mm"
include "wb.mm"
include "cvv.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wiso.mm"
include "elex.mm"
include "wepwsolem.mm"
include "isoso.mm"
include "3syl.mm"
include "adantr.mm"
include "mpbid.mm"

theorem wepwso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cT: class T
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let cU: class U
  assume wepwso.t: |- T = { <. x , y >. | E. z e. A ( ( z e. y /\ -. z e. x ) /\ A. w e. A ( w R z -> ( w e. x <-> w e. y ) ) ) }

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint a w
  disjoint b w
  disjoint c w
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint F b
  disjoint F c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint U a
  disjoint U b
  disjoint U c
  assert |- ( ( A e. V /\ R We A ) -> T Or ~P A )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    wwe
    #
    wa
    c2o
    cA
    cmap
    co
    #
    vz
    cv
    #
    vx
    cv
    #
    cfv
    @3
    vy
    cv
    #
    cfv
    cep
    wbr
    vw
    cv
    #
    @3
    cR
    wbr
    @6
    @4
    cfv
    @6
    @5
    cfv
    wceq
    wi
    vw
    cA
    wral
    wa
    vz
    cA
    wrex
    vx
    vy
    copab
    #
    wor
    #
    cA
    cpw
    #
    cT
    wor
    #
    @0
    @1
    c2o
    cep
    wor
    #
    @8
    c2o
    word
    #
    c2o
    cep
    wwe
    @11
    c2o
    com
    wcel
    @12
    2onn
    c2o
    nnord
    ax-mp
    c2o
    ordwe
    c2o
    cep
    weso
    mp2b
    vx
    vy
    vz
    vw
    cA
    c2o
    cR
    cep
    @7
    cV
    @7
    eqid
    #
    wemapso
    mp3an3
    @0
    @8
    @10
    wb
    #
    @1
    @0
    cA
    cvv
    wcel
    @2
    @9
    @7
    cT
    va
    @2
    va
    cv
    ccnv
    c1o
    csn
    cima
    cmpt
    #
    wiso
    @14
    cA
    cV
    elex
    vx
    vy
    vz
    vw
    cA
    cR
    cT
    @7
    @15
    va
    wepwso.t
    @13
    @15
    eqid
    wepwsolem
    @2
    @9
    @7
    cT
    @15
    isoso
    3syl
    adantr
    mpbid
end
